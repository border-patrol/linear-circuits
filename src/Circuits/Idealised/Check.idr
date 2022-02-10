module Circuits.Idealised.Check

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Views

import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Whole
import Toolkit.Data.Location
import Toolkit.Data.List.DeBruijn

import Ref

import Circuits.Split
import Circuits.Idealised.Types
import Circuits.Idealised.Terms
import Circuits.Idealised.AST

%default total

public export
data Entry : (String, (Ty, Usage)) -> Type where
  MkEntry : (name : String)
         -> (type : Ty)
         -> (u    : Usage)
                 -> Entry (name, (type,u))

public export
Env : List (String, (Ty, Usage)) -> Type
Env = Env (String, (Ty, Usage)) Entry

isEmpty : (s : String) -> DPair Ty (\t => Elem (s, (t, FREE)) []) -> Void
isEmpty _ (MkDPair _ _) impossible

lookupLaterFail : (DPair Ty (\t => Elem (s, (t, FREE)) xs) -> Void)
               -> (s = name -> Void)
               -> DPair Ty (\t => Elem (s, (t, FREE)) ((name, (type, u)) :: xs))
               -> Void
lookupLaterFail f g (MkDPair type Here) = g Refl
lookupLaterFail f g (MkDPair fst (There x)) = f (MkDPair fst x)

lookupLaterFailAlt : (DPair Ty (\t => Elem (s, (t, FREE)) xs) -> Void)
                   -> DPair Ty (\t => Elem (s, (t, FREE)) ((s, (type, USED)) :: xs)) -> Void
lookupLaterFailAlt f (MkDPair fst (There z)) = f (MkDPair fst z)

public export
data LookupFail = NotFound String | IsUsed String

lookup : (s : String)
      -> Env ctxt
      -> DecInfo LookupFail (t ** Elem (s,(t,FREE)) ctxt)
lookup s [] = No (NotFound s) (isEmpty s)
lookup s ((MkEntry name type u) :: rest) with (decEq s name)
  lookup s ((MkEntry s type u) :: rest) | (Yes Refl) with (u)
    lookup s ((MkEntry s type u) :: rest) | (Yes Refl) | USED with (lookup s rest)
      lookup s ((MkEntry s type u) :: rest) | (Yes Refl) | USED | (Yes (MkDPair fst snd))
        = Yes (MkDPair fst (There snd))
      lookup s ((MkEntry s type u) :: rest) | (Yes Refl) | USED | (No reason contra)
        = No (IsUsed s) (lookupLaterFailAlt contra)
    lookup s ((MkEntry s type u) :: rest) | (Yes Refl) | FREE
      = Yes (MkDPair type Here)

  lookup s ((MkEntry name type u) :: rest) | (No contra) with (lookup s rest)
    lookup s ((MkEntry name type u) :: rest) | (No contra) | (Yes (MkDPair fst snd))
      = Yes (MkDPair fst (There snd))
    lookup s ((MkEntry name type u) :: rest) | (No contra) | (No reason f)
      = No reason (lookupLaterFail f contra)

strip : {ctxt : List (String, (Ty, Usage))}
     -> Elem (s,(type,usage)) ctxt -> Elem (type,usage) (map Builtin.snd ctxt)
strip Here = Here
strip (There x) = There (strip x)

data Use : (curr : List (String, (Ty, Usage)))
        -> (prf  : Elem (s,(type,FREE)) curr)
        -> (next : List (String, (Ty, Usage)))
        -> Type
  where
    H : Use ((s,(type,FREE)) :: rest)
            Here
            ((s,(type,USED)) :: rest)
    T :  Use rest later restAlt
      -> Use ((s,(t,u)) :: rest)
             (There later)
             ((s,(t,u)) :: restAlt)

use : {curr : List (String, (Ty,Usage))}
   -> (prf : Elem (s,(t,FREE)) curr)
   -> (env : Env curr)
          -> DPair (List (String, (Ty,Usage)))
                   (Use curr prf)
use _ [] impossible

use {curr = ((s, (t, FREE)) :: xs)} Here (elem :: rest) = MkDPair ((s, (t, USED)) :: xs) H
use {curr = ((x, (z, w)) :: xs)} (There y) (elem :: rest) with (use y rest)
  use {curr = ((x, (z, w)) :: xs)} (There y) (elem :: rest) | (MkDPair fst snd) = MkDPair ((x, (z, w)) :: fst) (T snd)


strip' : {curr,next : List (String, (Ty,Usage))}
      -> {prf       : Elem (s,(t,FREE)) curr}
      -> Use curr prf next
      -> Use (map Builtin.snd curr)
             (strip prf)
             (map Builtin.snd next)
strip' H = H
strip' (T x) = T (strip' x)

newEnv : (env : Env curr)
      -> (use : Use curr prf next)
             -> Env next
newEnv (MkEntry s type FREE :: rest) H = MkEntry s type USED :: rest
newEnv (elem :: rest) (T x) = elem :: newEnv rest x

laterUsed : (All Used (map Builtin.snd xs) -> Void) -> All Used ((type, USED) :: map Builtin.snd xs) -> Void
laterUsed f (x :: y) = f y

isUsed : DList (String, (Ty, Usage)) Entry xs -> All Used ((type, FREE) :: map Builtin.snd xs) -> Void
isUsed [] (Types.IsUsed :: _) impossible
isUsed (_ :: _) (Types.IsUsed :: _) impossible

used : Env ctxt
    -> Dec (All Used (map Builtin.snd ctxt))
used [] = Yes []
used ((MkEntry name type USED) :: rest) with (used rest)
  used ((MkEntry name type USED) :: rest) | (Yes prf) = Yes (IsUsed :: prf)

  used ((MkEntry name type USED) :: rest) | (No contra) = No (laterUsed contra)

used ((MkEntry name type FREE) :: rest) = No (isUsed rest)

public export
data FailingEdgeCase = InvalidSplit Nat Nat Nat Nat
                     | InvalidEdge  Nat Nat Nat

public export
data Error = Mismatch Ty Ty | ElemFail LookupFail | PortExpected Direction
           | VectorExpected
           | VectorTooShort
           | VectorSizeMismatch Whole Whole Whole
           | LinearityError (Env es)
           | Err FileContext Check.Error
           | NotEdgeCase FailingEdgeCase
           | MismatchGate DType DType

public export
TyCheck : Type -> Type
TyCheck = Either Check.Error

lift : Dec a -> Check.Error -> TyCheck a
lift (Yes prf) _ = Right prf
lift (No contra) e = Left e

namespace Info
  public export
  lift : DecInfo e a -> Check.Error -> TyCheck a
  lift (Yes prf)     _ = Right prf
  lift (No m contra) e = Left e

  public export
  allEqual : FileContext
          -> (a,b,c : DType)
          -> TyCheck (AllEqual a b c)
  allEqual fc a b c with (Views.allEqual a b c)
    allEqual fc c c c | (Yes AE)
      = pure AE
    allEqual fc a b c | (No AB prfWhyNot)
      = Left (Err fc (MismatchGate a b))
    allEqual fc a b c | (No AC prfWhyNot)
      = Left (Err fc (MismatchGate a c))


typeCheck : {ctxt : List (String, (Ty,Usage))}
         -> (curr : Env ctxt)
         -> (ast  : AST)
                  -> TyCheck (type ** cout ** Pair (Env cout) (Term (map Builtin.snd ctxt)
                                                                    type
                                                                    (map Builtin.snd cout)))
typeCheck curr (Var x) with (lookup (get x) curr)
  typeCheck curr (Var x) | (Yes (MkDPair ty prf)) with (use prf curr)
    typeCheck curr (Var x) | (Yes (MkDPair ty prf)) | (MkDPair next u)
       = Right (ty ** next ** MkPair (newEnv curr u) (Var (strip prf) (strip' u)))

  typeCheck curr (Var x) | (No reason contra) = Left (Err (span x) (ElemFail reason))

typeCheck curr (Input fc x y s z)
  = do (TyUnit ** cz ** (ex,term)) <- typeCheck (MkEntry (get s) (TyPort (MkPair x y)) FREE :: curr) z
         | (ty ** _  ** _) => Left (Mismatch TyUnit ty)

       case ex of
         Nil => pure (TyUnit ** cz ** (Nil, (NewSignal x y term)))
         _   => Left (Err fc (LinearityError ex))



typeCheck curr (Wire fc x a b y)
  = do (TyUnit ** cz ** (ex,term)) <- typeCheck (MkEntry (get a) (TyPort (MkPair OUTPUT x)) FREE ::
                                               MkEntry (get b) (TyPort (MkPair INPUT  x)) FREE :: curr) y
         | (ty ** _  ** _) => Left (Mismatch TyUnit ty)

       case ex of
         Nil => pure (TyUnit ** cz ** (Nil, (Wire x term)))
         _   => Left (Err fc (LinearityError ex))

typeCheck curr (Dup fc x y z)
  = do (TyPort (OUTPUT,dtypeA) ** cx ** (ex,termX)) <- typeCheck curr x
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (OUTPUT,dtypeB) ** cy ** (ey,termY)) <- typeCheck ex y
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (INPUT,dtypeC) ** cz ** (ez,termZ)) <- typeCheck ey z
                  | ty => Left (Err fc (PortExpected INPUT))

       Refl <- lift (decEq dtypeA dtypeB)
                    (Err fc (MismatchGate dtypeA dtypeB))

       Refl <- lift (decEq dtypeB dtypeC)
                    (Err fc (MismatchGate dtypeA dtypeC))

       pure (TyGate ** cz ** (ez, Dup termX termY termZ))

typeCheck curr (Seq x y)
  = do (TyGate ** cx ** (ex,termX)) <- typeCheck curr x
            | (ty ** _ ** _) => Left (Mismatch TyGate ty)

       (TyUnit ** cy ** (ey, termY)) <- typeCheck ex y
             | (ty ** _ ** _) => Left (Mismatch TyUnit ty)

       case ey of
         Nil => pure (TyUnit ** cy ** (Nil, Seq termX termY))
         _   => Left ((LinearityError ey))


typeCheck curr (Not fc x y)
  = do (TyPort (OUTPUT,LOGIC) ** cx ** (ex,termX)) <- typeCheck curr x
         | (ty ** cx ** (ex,termX))
             => Left (Err fc (Mismatch (TyPort (OUTPUT,LOGIC)) ty))

       (TyPort (INPUT,LOGIC) ** cy ** (ey,termY)) <- typeCheck ex y
         | (ty ** cy ** (ey,termY))
             => Left (Err fc (Mismatch (TyPort (INPUT,LOGIC)) ty))

       pure (TyGate ** cy ** (ey,Not termX termY))

typeCheck curr (Gate fc k x y z)
  = do (TyPort (OUTPUT,LOGIC) ** cx ** (ex,termX)) <- typeCheck curr x
         | (ty ** cx ** (ex,termX)) => Left (Err fc (Mismatch (TyPort (OUTPUT, LOGIC)) ty))

       (TyPort (INPUT,LOGIC) ** cy ** (ey,termY)) <- typeCheck ex y
         | (ty ** cy ** (ey,termY))
             => Left (Err fc (Mismatch (TyPort (INPUT,LOGIC)) ty))

       (TyPort (INPUT,LOGIC) ** cz ** (ez,termZ)) <- typeCheck ey z
         | (ty ** cz ** (ez,termZ))
             => Left (Err fc (Mismatch (TyPort (INPUT,LOGIC)) ty))

       pure (TyGate ** cz ** (ez,Gate k termX termY termZ))

typeCheck curr (Mux fc v x y z)
  = do (TyPort (OUTPUT,dtypeA) ** cv ** (ev,termV)) <- typeCheck curr v
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (INPUT,LOGIC) ** cx ** (ex,termX)) <- typeCheck ev x
                  | (ty ** cx ** (ex,termX))
                       => Left (Err fc (Mismatch (TyPort (INPUT,LOGIC)) ty))

       (TyPort (INPUT,dtypeB) ** cy ** (ey,termY)) <- typeCheck ex y
                  | ty => Left (Err fc (PortExpected INPUT))

       (TyPort (INPUT,dtypeC) ** cz ** (ez,termZ)) <- typeCheck ey z
                  | ty => Left (Err fc (PortExpected INPUT))

       Refl <- lift (decEq dtypeA dtypeB)
                    (Err fc (MismatchGate dtypeA dtypeB))

       Refl <- lift (decEq dtypeB dtypeC)
                    (Err fc (MismatchGate dtypeA dtypeC))

       pure (TyGate ** cz ** (ez,Mux termV termX termY termZ))

typeCheck curr (IndexS fc o i)
  = do (TyPort (OUTPUT,dtypeO) ** co ** (eo,termO)) <- typeCheck curr o
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (INPUT,BVECT (W (S Z) ItIsSucc) dtypeI) ** ci ** (ei,termI)) <- typeCheck eo i
                  | (TyPort (INPUT, BVECT s type) ** cx ** (ex,termX))
                       => Left (Err fc (Mismatch (TyPort (INPUT,BVECT (W (S Z) ItIsSucc) type)) (TyPort (INPUT, BVECT s type))))
                  | ty => Left (Err fc (PortExpected INPUT))

       Refl <- lift (decEq dtypeO dtypeI)
                    (Err fc (MismatchGate dtypeO  dtypeI))

       pure (TyGate ** ci ** (ei,IndexSingleton termO termI))


typeCheck curr (IndexE fc k a b i)
  = do (TyPort (OUTPUT,dtypeA) ** cA ** (eA,termA)) <- typeCheck curr a
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (OUTPUT,BVECT free dtypeB) ** cB ** (eB,termB)) <- typeCheck eA b
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (INPUT,BVECT size dtypeC) ** cC ** (eC,termC)) <- typeCheck eB i
                  | ty => Left (Err fc (PortExpected INPUT))

       Refl <- lift (decEq dtypeA dtypeB)
                    (Err fc (MismatchGate dtypeA dtypeB))

       Refl <- lift (decEq dtypeB dtypeC)
                    (Err fc (MismatchGate dtypeB dtypeC))

       let p = case k of { F => minus (toNat size) 1; L => 0}

       (s ** prf) <- Info.lift (EdgeCase.index size p)
                               (Err fc (NotEdgeCase (InvalidEdge (toNat size) (S Z) (toNat free))))

       Refl <- lift (decEq free s)
                    (Err fc (NotEdgeCase (InvalidEdge (toNat size) (S Z) (toNat free))))

       pure (TyGate ** cC ** (eC,IndexEdge p prf termA termB termC))

typeCheck curr (IndexP fc p a b c i)
  = do (TyPort (OUTPUT,dtypeA) ** cA ** (eA,termA)) <- typeCheck curr a
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (OUTPUT,BVECT freeB dtypeB) ** cB ** (eB,termB)) <- typeCheck eA b
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (OUTPUT,BVECT freeC dtypeC) ** cC ** (eC,termC)) <- typeCheck eB c
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (INPUT,BVECT size dtypeD) ** cI ** (eI,termI)) <- typeCheck eC i
                  | ty => Left (Err fc (PortExpected INPUT))

       Refl <- lift (decEq dtypeA dtypeB)
                    (Err fc (MismatchGate dtypeA (BVECT freeB dtypeB)))

       Refl <- lift (decEq dtypeB dtypeC)
                    (Err fc (MismatchGate (BVECT freeB dtypeB) (BVECT freeC dtypeC)))

       Refl <- lift (decEq dtypeC dtypeD)
                    (Err fc (MismatchGate (BVECT freeC dtypeC) (BVECT size dtypeD)))

       (a ** b ** prf) <- Info.lift (Pivot.index p size)
                                    (Err fc (NotEdgeCase (InvalidSplit p (toNat size) (toNat freeB) (toNat freeC))))

       Refl <- lift (decEq freeB a)
                    (Err fc (MismatchGate (BVECT a     dtypeB)
                                          (BVECT freeB dtypeB)))

       Refl <- lift (decEq freeC b)
                    (Err fc (MismatchGate (BVECT b     dtypeB)
                                          (BVECT freeC dtypeB)))

       pure (TyGate ** cI ** (eI,IndexSplit p prf termA termB termC termI))

typeCheck curr (MergeS fc o i)
  = do (TyPort (OUTPUT,BVECT (W (S Z) ItIsSucc) dtypeO) ** cO ** (eO,termO)) <- typeCheck curr o
           | (TyPort (INPUT, BVECT s type) ** cx ** (ex,termX))
                => Left (Err fc (Mismatch (TyPort (OUTPUT, BVECT (W (S Z) ItIsSucc) type))
                                          (TyPort (INPUT,  BVECT s                  type))))
           | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (INPUT, dtypeI) ** cI ** (eI, termI)) <- typeCheck eO i
           | ty => Left (Err fc (PortExpected INPUT))

       Refl <- lift (decEq dtypeO dtypeI)
                    (Err fc (MismatchGate dtypeO dtypeI))

       pure (TyGate ** cI ** (eI, MergeSingleton termO termI))

typeCheck curr (MergeV fc o a b)
  = do (TyPort (OUTPUT, dtypeO) ** cO ** (eO, termO)) <- typeCheck curr o
           | ty => Left (Err fc (PortExpected OUTPUT))

       (TyPort (INPUT, dtypeA) ** cA ** (eA, termA)) <- typeCheck eO a
           | ty => Left (Err fc (PortExpected INPUT))

       (TyPort (INPUT, dtypeB) ** cB ** (eB, termB)) <- typeCheck eA b
           | ty => Left (Err fc (PortExpected INPUT))

       case Views.allEqual LOGIC dtypeA dtypeB of
            -- Case when merging two logic wires into a vector of size two
            (Yes AE) =>
              do Refl <- lift (decEq dtypeO (BVECT (W (S (S Z)) ItIsSucc) LOGIC))
                              (Err fc (MismatchGate (BVECT (W (S (S Z)) ItIsSucc) LOGIC)
                                                    dtypeO))

                 pure (TyGate ** cB ** (eB, Merge2L2V termO termA termB))

            -- Case when merging two vectors. coudl be cleaner.
            (No msgWhyNot prfWhyNot) =>
                case dtypeO of
                  LOGIC => Left (Err fc VectorExpected)
                  BVECT sizeO typeO =>
                    case dtypeA of
                      LOGIC => Left (Err fc VectorExpected)
                      BVECT sizeA typeA =>
                        case dtypeB of
                          LOGIC => Left (Err fc VectorExpected)
                          BVECT sizeB typeB =>
                            do prfSize <- lift (isPlus sizeA sizeB sizeO)
                                               (Err fc (VectorSizeMismatch sizeO sizeA sizeB))
                               AE <- allEqual fc typeO typeA typeB

                               pure (TyGate ** cB ** (eB, Merge2V2V prfSize termO termA termB))

typeCheck curr (Stop fc) with (used curr)
  typeCheck curr (Stop fc) | (Yes prf) = Right (TyUnit ** _ ** (Nil, Stop prf))
  typeCheck curr (Stop fc) | (No contra) = Left (Err fc (LinearityError curr))



namespace Design
  export
  typeCheck : (ast : AST) -> TyCheck (Term Nil TyUnit Nil)
  typeCheck ast with (typeCheck Nil ast)
    typeCheck ast | (Left x) = Left x
    typeCheck ast | (Right (MkDPair TyUnit (MkDPair Nil (env,term)))) = Right term
    typeCheck ast | (Right (MkDPair ty snd)) = Left (Mismatch TyUnit ty)

  export
  typeCheckIO : (ast : AST) -> IO (TyCheck (Term Nil TyUnit Nil))
  typeCheckIO ast = pure (typeCheck ast)

-- [ EOF ]
