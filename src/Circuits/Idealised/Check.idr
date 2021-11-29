module Circuits.Idealised.Check

import Decidable.Equality

import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Data.List.DeBruijn
import Utilities
import EdgeBoundedGraph

import Circuits.Types
import Circuits.Idealised

%default total

public export
data AST = Var String
         | Input Direction DType String AST
         | Wire DType String String AST
         | Seq AST AST
         | Not AST AST
         | Gate AST AST AST
         | Stop

data Entry : (String, (Ty, Usage)) -> Type where
  MkEntry : (name : String)
         -> (type : Ty)
         -> (u    : Usage)
                 -> Entry (name, (type,u))

Env : List (String, (Ty, Usage)) -> Type
Env = Env (String, (Ty, Usage)) Entry

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


data Error = Mismatch Ty Ty | Undeclared String | PortExpected Direction
           | LinearityError

public export
TyCheck : Type -> Type
TyCheck = Either Error

export
typeCheck : {ctxt : List (String, (Ty,Usage))}
         -> (curr : Env ctxt)
         -> (ast  : AST)
                  -> TyCheck (type ** cout ** Pair (Env cout) (Term (map Builtin.snd ctxt) type (map Builtin.snd cout)))
typeCheck curr (Var x) with (lookup x curr)
  typeCheck curr (Var x) | (Yes (MkDPair ty prf)) with (use prf curr)
    typeCheck curr (Var x) | (Yes (MkDPair ty prf)) | (MkDPair next u)
       = Right (ty ** next ** MkPair (newEnv curr u) (Var (strip prf) (strip' u)))

  typeCheck curr (Var x) | (No contra) = Left (Undeclared x)

typeCheck curr (Input x y s z)
  = do (Unit ** cz ** (ex,term)) <- typeCheck (MkEntry s (Port (MkPair x y)) FREE :: curr) z
         | (ty ** _  ** _) => Left (Mismatch Unit ty)

       case ex of
         Nil => pure (Unit ** cz ** (Nil, (NewSignal x y term)))
         _   => Left LinearityError



typeCheck curr (Wire x a b y)
  = do (Unit ** cz ** (ex,term)) <- typeCheck (MkEntry a (Port (MkPair OUTPUT x)) FREE ::
                                               MkEntry b (Port (MkPair INPUT  x)) FREE :: curr) y
         | (ty ** _  ** _) => Left (Mismatch Unit ty)

       case ex of
         Nil => pure (Unit ** cz ** (Nil, (Wire x term)))
         _   => Left LinearityError


typeCheck curr (Seq x y)
  = do (Gate ** cx ** (ex,termX)) <- typeCheck curr x
         | (ty ** _ ** _) => Left (Mismatch Gate ty)
       (Unit ** cy ** (ey, termY)) <- typeCheck ex y
         | (ty ** _ ** _) => Left (Mismatch Unit ty)

       case ey of
         Nil => pure (Unit ** cy ** (Nil, Seq termX termY))
         _   => Left LinearityError


typeCheck curr (Not x y)
  = do (Port (OUTPUT,dtypeA) ** cx ** (ex,termX)) <- typeCheck curr x
                  | ty => Left (PortExpected OUTPUT)

       (Port (INPUT,dtypeB) ** cy ** (ey,termY)) <- typeCheck ex y
                  | ty => Left (PortExpected INPUT)

       case decEq dtypeA dtypeB of
         Yes Refl => pure (Gate ** cy ** (ey,Not termX termY))
         No contra => Left (Mismatch (Port (OUTPUT,dtypeA)) (Port (OUTPUT, dtypeB)))

typeCheck curr (Gate x y z)
  = do (Port (OUTPUT,dtypeA) ** cx ** (ex,termX)) <- typeCheck curr x
                  | ty => Left (PortExpected OUTPUT)

       (Port (INPUT,dtypeB) ** cy ** (ey,termY)) <- typeCheck ex y
                  | ty => Left (PortExpected INPUT)

       (Port (INPUT,dtypeC) ** cz ** (ez,termz)) <- typeCheck ey z
                  | ty => Left (PortExpected INPUT)

       case decEq dtypeA dtypeB of
         Yes Refl =>
           case decEq dtypeB dtypeC of
             Yes Refl => pure (Gate ** cy ** (ey,Not termX termY))
             No contra => Left (Mismatch (Port (OUTPUT,dtypeA)) (Port (INPUT, dtypeC)))
         No contra => Left (Mismatch (Port (OUTPUT,dtypeA)) (Port (INPUT, dtypeB)))

typeCheck curr Stop with (used curr)
  typeCheck curr Stop | (Yes prf) = Right (Unit ** _ ** (Nil, Stop prf))
  typeCheck curr Stop | (No contra) = Left LinearityError


-- [ EOF ]
