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

import Toolkit.DeBruijn.Context

import Circuits.Split
import Circuits.Idealised.Types
import Circuits.Idealised.Terms
import Circuits.Idealised.AST

%default total

public export
Context : List (Ty, Usage) -> Type
Context = Context (Ty,Usage)

public export
data LookupFail = NotFound String | IsUsed String

data IsFree : (str  : String)
           -> (item : Item (Ty,Usage) tu)
                   -> Type
  where
    IF : (prf : x = y)
      -> (prfU : u = FREE)
              -> IsFree x (I y (type, u))

isFree : (str  : String)
      -> (item : Item (Ty,Usage) tu)
              -> DecInfo (LookupFail)
                         (IsFree str item)
isFree str (I name tu) with (decEq str name)
  isFree str (I str (t,u)) | (Yes Refl) with (u)
    isFree str (I str (t,u)) | (Yes Refl) | USED
        = No (IsUsed str) (isNotFree)
      where
        isNotFree : IsFree str (I str (t, USED)) -> Void
        isNotFree (IF _ Refl) impossible

    isFree str (I str (t,u)) | (Yes Refl) | FREE
      = Yes (IF Refl Refl)

  isFree str (I name tu) | (No contra)
    = No (NotFound str) (\(IF Refl _) => contra Refl)

FreeVar : String -> Context types -> Type
FreeVar str ctxt
  = Exists (IsFree str) ctxt

lookup : (s    : String)
      -> {types : List (Ty,Usage)}
      -> (ctxt : Context types)
              -> DecInfo (Error LookupFail) (FreeVar s ctxt)
lookup s ctxt with (exists (isFree s) ctxt)
  lookup s ctxt | (Yes (B item prfP prfE))
    = Yes (B item prfP prfE)
  lookup s ctxt | (No msg contra)
      = No msg (lookupFailed contra)
    where
      lookupFailed : (Exists (IsFree s) ctxt -> Void) -> Exists (IsFree s) ctxt -> Void
      lookupFailed f (B item prfP prfE) = f (B item prfP prfE)

useEnv : (env : Context curr)
      -> (use : Use curr prf next)
             -> Context next
useEnv ((I n (t,FREE)) :: rest) H
  = I n (t, USED) :: rest

useEnv (elem :: rest) (T x)
  = elem :: useEnv rest x

isUsed : (env : Context curr)
             -> Dec (All Used curr)
isUsed []
  = Yes []

isUsed ((I _ i) :: rest) with (used i)
  isUsed ((I _ i) :: rest) | (Yes prf) with (isUsed rest)
    isUsed ((I _ i) :: rest) | (Yes prf) | (Yes x)
      = Yes (prf :: x)

    isUsed ((I _ i) :: rest) | (Yes prf) | (No contra)
        = No (\(x::xs) => contra xs)

  isUsed ((I _ i) :: rest) | (No contra)
    = No (\(x::xs) => contra x)

public export
data FailingEdgeCase = InvalidSplit Nat Nat Nat Nat
                     | InvalidEdge  Nat Nat Nat

public export
data Error = Mismatch Ty Ty | ElemFail (Error LookupFail) | PortExpected Direction
           | VectorExpected
           | VectorTooShort
           | VectorSizeMismatch Whole Whole Whole
           | LinearityError (Context types)
           | Err FileContext Check.Error
           | NotEdgeCase FailingEdgeCase
           | MismatchGate DType DType


public export
TyCheck : Type -> Type
TyCheck = Either Check.Error

lift : Dec a -> Check.Error -> TyCheck a
lift (Yes prf) _ = Right prf
lift (No contra) e = Left e

throw : FileContext -> Check.Error -> TyCheck a
throw fc e = Left $ Err fc e

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

data Result : (curr : List (Ty,Usage))
           -> Type
  where
    R : {cout : _}
     -> (type : Ty)
     -> (new  : Context cout)
     -> (term : Term cin type cout)
             -> Result cin

typeCheck : {cin  : List (Ty,Usage)}
         -> (curr : Context cin)
         -> (ast  : AST)
         -> TyCheck (Result cin)
typeCheck curr (Var x) with (lookup (get x) curr)
  typeCheck curr (Var x) | (Yes nidx) with (mkNameless nidx)
    typeCheck curr (Var x) | (Yes nidx) | (N (I y (type, u)) (IF prf prfU) idx) with (prfU)
      typeCheck curr (Var x) | (Yes nidx) | (N (I y (type, FREE)) (IF prf prfU) idx) | Refl with (use idx)
        typeCheck curr (Var x) | (Yes nidx) | (N (I y (type, FREE)) (IF prf prfU) idx) | Refl | (MkDPair cout used) with (useEnv curr used)
          typeCheck curr (Var x) | (Yes nidx) | (N (I y (type, FREE)) (IF prf prfU) idx) | Refl | (MkDPair cout used) | new
            = pure (R type new (Var idx used))


  typeCheck curr (Var x) | (No m _)
    = Left (Err (span x) (ElemFail m))

typeCheck curr (Seq x y)
  = do (R TyGate ex termX) <- typeCheck curr x
            | (R ty _ _) => Left (Mismatch TyGate ty)

       (R TyUnit ey termY) <- typeCheck ex y
             | (R ty _ _) => Left (Mismatch TyUnit ty)

       case ey of
         Nil => pure (R TyUnit Nil (Seq termX termY))
         _   => Left (LinearityError ey)


typeCheck curr (Input fc x y name body)
  = do (R TyUnit next term) <- typeCheck (I (get name) ((TyPort (MkPair x y)),FREE) :: curr)
                                         body
           | (R ty _ _) => Left (Mismatch TyUnit ty)
       case next of
         [] => pure (R TyUnit Nil (NewSignal x y term))
         _  => throw fc (LinearityError next)

typeCheck curr (Wire fc type a b body)

  = do (R TyUnit next term) <- typeCheck (I (get a) ((TyPort (MkPair OUTPUT type)), FREE) ::
                                          I (get b) ((TyPort (MkPair INPUT  type)), FREE) :: curr)
                                          body
           | (R ty _ _) => Left (Mismatch TyUnit ty)

       case next of
         Nil => pure (R TyUnit Nil (Wire type term))
         _   => throw fc (LinearityError next)


typeCheck curr (Mux fc o c a b)
  = do (R (TyPort (OUTPUT,dtypeA)) cO termO) <- typeCheck curr o
                  | ty => throw fc (PortExpected OUTPUT)

       (R (TyPort (INPUT,LOGIC)) cC termC) <- typeCheck cO c
                  | (R ty _ _)
                       => throw fc (Mismatch (TyPort (INPUT,LOGIC)) ty)

       (R (TyPort (INPUT,dtypeB)) cA termA) <- typeCheck cC a
                  | ty => throw fc (PortExpected INPUT)

       (R (TyPort (INPUT,dtypeC)) cB termB) <- typeCheck cA b
                  | ty => throw fc (PortExpected INPUT)

       Refl <- lift (decEq dtypeA dtypeB)
                    (Err fc (MismatchGate dtypeA dtypeB))

       Refl <- lift (decEq dtypeB dtypeC)
                    (Err fc (MismatchGate dtypeA dtypeC))

       pure (R TyGate cB (Mux termO termC termA termB))

typeCheck curr (Dup fc a b i)
  = do R (TyPort (OUTPUT,dtypeA)) cA termA <- typeCheck curr a
                  | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (OUTPUT,dtypeB)) cB termB <- typeCheck cA b
                  | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (INPUT,dtypeC)) cI termI <- typeCheck cB i
                  | ty => throw fc (PortExpected INPUT)

       Refl <- lift (decEq dtypeA dtypeB)
                    (Err fc (MismatchGate dtypeA dtypeB))

       Refl <- lift (decEq dtypeB dtypeC)
                    (Err fc (MismatchGate dtypeA dtypeC))

       pure (R TyGate cI (Dup termA termB termI))


typeCheck curr (Not fc a b)
  = do R (TyPort (OUTPUT,LOGIC)) cA termA <- typeCheck curr a
                  | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (INPUT,LOGIC)) cB termB <- typeCheck cA b
                  | ty => throw fc (PortExpected INPUT)

       pure (R TyGate cB (Not termA termB))

typeCheck curr (Gate fc k a b c)
  = do R (TyPort (OUTPUT,LOGIC)) cA termA <- typeCheck curr a
                  | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (INPUT,LOGIC)) cB termB <- typeCheck cA b
                  | ty => throw fc (PortExpected INPUT)

       R (TyPort (INPUT,LOGIC)) cC termC <- typeCheck cB c
                  | ty => throw fc (PortExpected INPUT)


       pure (R TyGate cC (Gate k termA termB termC))



typeCheck curr (IndexS fc o i)
  = do R (TyPort (OUTPUT,dtypeO)) cO termO <- typeCheck curr o
                  | ty => Left (Err fc (PortExpected OUTPUT))

       R (TyPort (INPUT,BVECT (W (S Z) ItIsSucc) dtypeI)) cI termI <- typeCheck cO i
                  | R (TyPort (INPUT, BVECT s type)) _ _
                       => throw fc (Mismatch (TyPort (INPUT, BVECT (W (S Z) ItIsSucc) type))
                                             (TyPort (INPUT, BVECT s type)))
                  | ty => throw fc (PortExpected INPUT)

       Refl <- lift (decEq dtypeO dtypeI)
                    (Err fc (MismatchGate dtypeO  dtypeI))

       pure (R TyGate cI (IndexSingleton termO termI))

typeCheck curr (IndexE fc k a b i)

  = do R (TyPort (OUTPUT,dtypeA)) cA termA <- typeCheck curr a
                  | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (OUTPUT,BVECT free dtypeB)) cB termB <- typeCheck cA b
                  | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (INPUT,BVECT size dtypeC)) cI termI <- typeCheck cB i
                  | ty => throw fc (PortExpected INPUT)

       Refl <- lift (decEq dtypeA dtypeB)
                    (Err fc (MismatchGate dtypeA dtypeB))

       Refl <- lift (decEq dtypeB dtypeC)
                    (Err fc (MismatchGate dtypeB dtypeC))

       let p = case k of { F => minus (toNat size) 1; L => 0}

       (s ** prf) <- Info.lift (EdgeCase.index size p)
                               (Err fc (NotEdgeCase (InvalidEdge (toNat size) (S Z) (toNat free))))

       Refl <- lift (decEq free s)
                    (Err fc (NotEdgeCase (InvalidEdge (toNat size) (S Z) (toNat free))))

       pure (R TyGate cI (IndexEdge p prf termA termB termI))


typeCheck curr (IndexP fc p a b c i)

  = do R (TyPort (OUTPUT,dtypeA)) cA termA <- typeCheck curr a
                  | ty => Left (Err fc (PortExpected OUTPUT))

       R (TyPort (OUTPUT,BVECT freeB dtypeB)) cB termB <- typeCheck cA b
                  | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (OUTPUT,BVECT freeC dtypeC)) cC termC <- typeCheck cB c
                  | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (INPUT,BVECT size dtypeD)) cI termI <- typeCheck cC i
                  | ty => throw fc (PortExpected INPUT)

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

       pure (R TyGate cI (IndexSplit p prf termA termB termC termI))

typeCheck curr (MergeS fc o i)

  = do R (TyPort (OUTPUT,BVECT (W (S Z) ItIsSucc) dtypeO)) cO termO <- typeCheck curr o
           | R (TyPort (INPUT, BVECT s type)) _ _
                => throw fc (Mismatch (TyPort (OUTPUT, BVECT (W (S Z) ItIsSucc) type))
                                      (TyPort (INPUT,  BVECT s                  type)))
           | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (INPUT, dtypeI)) cI termI <- typeCheck cO i
           | ty => throw fc (PortExpected INPUT)

       Refl <- lift (decEq dtypeO dtypeI)
                    (Err fc (MismatchGate dtypeO dtypeI))

       pure (R TyGate cI (MergeSingleton termO termI))


typeCheck curr (MergeV fc o a b)
  = do R (TyPort (OUTPUT, dtypeO)) cO termO <- typeCheck curr o
           | ty => throw fc (PortExpected OUTPUT)

       R (TyPort (INPUT, dtypeA)) cA termA <- typeCheck cO a
           | ty => throw fc (PortExpected INPUT)

       R (TyPort (INPUT, dtypeB)) cB termB <- typeCheck cA b
           | ty => throw fc (PortExpected INPUT)

       case Views.allEqual LOGIC dtypeA dtypeB of
            -- Case when merging two logic wires into a vector of size two
            (Yes AE) =>
              do Refl <- lift (decEq dtypeO (BVECT (W (S (S Z)) ItIsSucc) LOGIC))
                              (Err fc (MismatchGate (BVECT (W (S (S Z)) ItIsSucc) LOGIC)
                                                    dtypeO))

                 pure (R TyGate cB (Merge2L2V termO termA termB))

            -- Case when merging two vectors. coudl be cleaner.
            (No msgWhyNot prfWhyNot) =>
                case dtypeO of
                  LOGIC => throw fc VectorExpected
                  BVECT sizeO typeO =>
                    case dtypeA of
                      LOGIC => throw fc VectorExpected
                      BVECT sizeA typeA =>
                        case dtypeB of
                          LOGIC => throw fc VectorExpected
                          BVECT sizeB typeB =>
                            do prfSize <- lift (isPlus sizeA sizeB sizeO)
                                               (Err fc (VectorSizeMismatch sizeO sizeA sizeB))
                               AE <- allEqual fc typeO typeA typeB

                               pure (R TyGate cB (Merge2V2V prfSize termO termA termB))

typeCheck curr (Stop x) with (isUsed curr)
  typeCheck curr (Stop x) | (Yes prf)
    = Right (R TyUnit Nil (Stop prf))

  typeCheck curr (Stop fc) | (No contra)
    = throw fc (LinearityError curr)

namespace Design
  export
  typeCheck : (ast : AST) -> TyCheck (Term Nil TyUnit Nil)
  typeCheck ast with (typeCheck Nil ast)
    typeCheck ast | (Left x)
      = Left x

    typeCheck ast | (Right (R TyUnit Nil term))
      = Right term

    typeCheck ast | (Right (R ty _ _))
      = Left (Mismatch TyUnit ty)

  export
  typeCheckIO : (ast : AST) -> IO (TyCheck (Term Nil TyUnit Nil))
  typeCheckIO ast = pure (typeCheck ast)

-- [ EOF ]
