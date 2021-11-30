module Circuits.Idealised.Check

import Decidable.Equality

import Data.String
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Data.Location
import Toolkit.Data.List.DeBruijn

import Ref
import Utilities
import EdgeBoundedGraph

import Circuits.Types
import Circuits.Idealised
import Circuits.Idealised.AST

%default total

data Entry : (String, (Ty, Usage)) -> Type where
  MkEntry : (name : String)
         -> (type : Ty)
         -> (u    : Usage)
                 -> Entry (name, (type,u))

Env : List (String, (Ty, Usage)) -> Type
Env = Env (String, (Ty, Usage)) Entry

showEnv : Env es -> String
showEnv [] = ""
showEnv ((MkEntry name type FREE) :: rest)
  = name <+> " is free\n" <+> (showEnv rest)
showEnv ((MkEntry name type USED) :: rest) = showEnv rest


isEmpty : (s : String) -> DPair Ty (\t => Elem (s, (t, FREE)) []) -> Void
isEmpty _ (MkDPair _ _) impossible

lookupLaterFail : (DPair Ty (\t => Elem (s, (t, FREE)) xs) -> Void) -> (s = name -> Void) -> DPair Ty (\t => Elem (s, (t, FREE)) ((name, (type, u)) :: xs)) -> Void
lookupLaterFail f g (MkDPair type Here) = g Refl
lookupLaterFail f g (MkDPair fst (There x)) = f (MkDPair fst x)

lookupLaterFailAlt : (DPair Ty (\t => Elem (s, (t, FREE)) xs) -> Void)
                   -> DPair Ty (\t => Elem (s, (t, FREE)) ((s, (type, USED)) :: xs)) -> Void
lookupLaterFailAlt f (MkDPair fst (There z)) = f (MkDPair fst z)

lookup : (s : String)
      -> Env ctxt
      -> Dec (t ** Elem (s,(t,FREE)) ctxt)
lookup s [] = No (isEmpty s)
lookup s ((MkEntry name type u) :: rest) with (decEq s name)
  lookup s ((MkEntry s type u) :: rest) | (Yes Refl) with (u)
    lookup s ((MkEntry s type u) :: rest) | (Yes Refl) | USED with (lookup s rest)
      lookup s ((MkEntry s type u) :: rest) | (Yes Refl) | USED | (Yes (MkDPair fst snd))
        = Yes (MkDPair fst (There snd))
      lookup s ((MkEntry s type u) :: rest) | (Yes Refl) | USED | (No contra)
        = No (lookupLaterFailAlt contra)
    lookup s ((MkEntry s type u) :: rest) | (Yes Refl) | FREE
      = Yes (MkDPair type Here)

  lookup s ((MkEntry name type u) :: rest) | (No contra) with (lookup s rest)
    lookup s ((MkEntry name type u) :: rest) | (No contra) | (Yes (MkDPair fst snd))
      = Yes (MkDPair fst (There snd))
    lookup s ((MkEntry name type u) :: rest) | (No contra) | (No f)
      = No (lookupLaterFail f contra)

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
isUsed [] (IsUsed :: _) impossible
isUsed (_ :: _) (IsUsed :: _) impossible

used : Env ctxt
    -> Dec (All Used (map Builtin.snd ctxt))
used [] = Yes []
used ((MkEntry name type USED) :: rest) with (used rest)
  used ((MkEntry name type USED) :: rest) | (Yes prf) = Yes (IsUsed :: prf)

  used ((MkEntry name type USED) :: rest) | (No contra) = No (laterUsed contra)

used ((MkEntry name type FREE) :: rest) = No (isUsed rest)

export
data Error = Mismatch Ty Ty | Undeclared String | PortExpected Direction
           | LinearityError (Env es)
           | Err FileContext Error
export
Show Error where
  show (Mismatch x y) = "Type Mismatch"
  show (Undeclared x) = "Undeclared name: " <+> x
  show (PortExpected INPUT) = "Expected Input"
  show (PortExpected OUTPUT) = "Expected Output"
  show (LinearityError env) = "Linearity Error:\n" <+> showEnv env
  show (Err x y) = unlines [show x <+> ": ", show y]

public export
TyCheck : Type -> Type
TyCheck = Either Error

typeCheck : {ctxt : List (String, (Ty,Usage))}
         -> (curr : Env ctxt)
         -> (ast  : AST)
                  -> TyCheck (type ** cout ** Pair (Env cout) (Term (map Builtin.snd ctxt) type (map Builtin.snd cout)))
typeCheck curr (Var x) with (lookup (get x) curr)
  typeCheck curr (Var x) | (Yes (MkDPair ty prf)) with (use prf curr)
    typeCheck curr (Var x) | (Yes (MkDPair ty prf)) | (MkDPair next u)
       = Right (ty ** next ** MkPair (newEnv curr u) (Var (strip prf) (strip' u)))

  typeCheck curr (Var x) | (No contra) = Left (Err (span x) (Undeclared (get x)))

typeCheck curr (Input fc x y s z)
  = do (Unit ** cz ** (ex,term)) <- typeCheck (MkEntry (get s) (Port (MkPair x y)) FREE :: curr) z
         | (ty ** _  ** _) => Left (Mismatch Unit ty)

       case ex of
         Nil => pure (Unit ** cz ** (Nil, (NewSignal x y term)))
         _   => Left (Err fc (LinearityError ex))



typeCheck curr (Wire fc x a b y)
  = do (Unit ** cz ** (ex,term)) <- typeCheck (MkEntry (get a) (Port (MkPair OUTPUT x)) FREE ::
                                               MkEntry (get b) (Port (MkPair INPUT  x)) FREE :: curr) y
         | (ty ** _  ** _) => Left (Mismatch Unit ty)

       case ex of
         Nil => pure (Unit ** cz ** (Nil, (Wire x term)))
         _   => Left (Err fc (LinearityError ex))

typeCheck curr (Dup fc x y z)
  = do (Port (OUTPUT,dtypeA) ** cx ** (ex,termX)) <- typeCheck curr x
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (Port (OUTPUT,dtypeB) ** cy ** (ey,termY)) <- typeCheck ex y
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (Port (INPUT,dtypeC) ** cz ** (ez,termZ)) <- typeCheck ey z
                  | ty => Left (Err fc (PortExpected INPUT))

       case decEq dtypeA dtypeB of
         Yes Refl =>
           case decEq dtypeB dtypeC of
             Yes Refl => pure (Gate ** cz ** (ez, Dup termX termY termZ))
             No contra => Left (Err fc (Mismatch (Port (OUTPUT,dtypeA)) (Port (INPUT, dtypeC))))
         No contra => Left (Err fc (Mismatch (Port (OUTPUT,dtypeA)) (Port (OUTPUT, dtypeB))))

typeCheck curr (Seq x y)
  = do (Gate ** cx ** (ex,termX)) <- typeCheck curr x
         | (ty ** _ ** _) => Left (Mismatch Gate ty)
       (Unit ** cy ** (ey, termY)) <- typeCheck ex y
         | (ty ** _ ** _) => Left (Mismatch Unit ty)

       case ey of
         Nil => pure (Unit ** cy ** (Nil, Seq termX termY))
         _   => Left ((LinearityError ey))


typeCheck curr (Not fc x y)
  = do (Port (OUTPUT,dtypeA) ** cx ** (ex,termX)) <- typeCheck curr x
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (Port (INPUT,dtypeB) ** cy ** (ey,termY)) <- typeCheck ex y
                  | ty => Left (Err fc (PortExpected INPUT))

       case decEq dtypeA dtypeB of
         Yes Refl => pure (Gate ** cy ** (ey,Not termX termY))
         No contra => Left (Err fc (Mismatch (Port (OUTPUT,dtypeA)) (Port (OUTPUT, dtypeB))))

typeCheck curr (Gate fc x y z)
  = do (Port (OUTPUT,dtypeA) ** cx ** (ex,termX)) <- typeCheck curr x
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (Port (INPUT,dtypeB) ** cy ** (ey,termY)) <- typeCheck ex y
                  | ty => Left (Err fc (PortExpected INPUT))

       (Port (INPUT,dtypeC) ** cz ** (ez,termZ)) <- typeCheck ey z
                  | ty => Left (Err fc (PortExpected INPUT))

       case decEq dtypeA dtypeB of
         Yes Refl =>
           case decEq dtypeB dtypeC of
             Yes Refl => pure (Gate ** cz ** (ez,Gate termX termY termZ))
             No contra => Left (Err fc (Mismatch (Port (OUTPUT,dtypeA)) (Port (INPUT, dtypeC))))
         No contra => Left (Err fc (Mismatch (Port (OUTPUT,dtypeA)) (Port (INPUT, dtypeB))))

typeCheck curr (Mux fc v x y z)
  = do (Port (OUTPUT,dtypeA) ** cv ** (ev,termV)) <- typeCheck curr v
                  | ty => Left (Err fc (PortExpected OUTPUT))

       (Port (INPUT,LOGIC) ** cx ** (ex,termX)) <- typeCheck ev x
                  | (Port (INPUT,type) ** cx ** (ex,termX)) => Left (Err fc (Mismatch (Port (INPUT,LOGIC)) (Port (INPUT,type))))
                  | ty => Left (Err fc (PortExpected INPUT))
       (Port (INPUT,dtypeB) ** cy ** (ey,termY)) <- typeCheck ex y
                  | ty => Left (Err fc (PortExpected INPUT))

       (Port (INPUT,dtypeC) ** cz ** (ez,termZ)) <- typeCheck ey z
                  | ty => Left (Err fc (PortExpected INPUT))

       case decEq dtypeA dtypeB of
         Yes Refl =>
           case decEq dtypeB dtypeC of
             Yes Refl => pure (Gate ** cz ** (ez,Mux termV termX termY termZ))
             No contra => Left (Err fc (Mismatch (Port (OUTPUT,dtypeA)) (Port (INPUT, dtypeC))))
         No contra => Left (Err fc (Mismatch (Port (OUTPUT,dtypeA)) (Port (INPUT, dtypeB))))


typeCheck curr (Stop fc) with (used curr)
  typeCheck curr (Stop fc) | (Yes prf) = Right (Unit ** _ ** (Nil, Stop prf))
  typeCheck curr (Stop fc) | (No contra) = Left (Err fc (LinearityError curr))

namespace Design
  export
  typeCheck : (ast : AST) -> TyCheck (Term Nil Unit Nil)
  typeCheck ast with (typeCheck Nil ast)
    typeCheck ast | (Left x) = Left x
    typeCheck ast | (Right (MkDPair Unit (MkDPair Nil (env,term)))) = Right term
    typeCheck ast | (Right (MkDPair ty snd)) = Left (Mismatch Unit ty)

  export
  typeCheckIO : (ast : AST) -> IO (TyCheck (Term Nil Unit Nil))
  typeCheckIO ast = pure (typeCheck ast)

-- [ EOF ]
