module Circuits.NetList.Check

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List.Elem
import Data.List.Quantifiers
import Data.Fin

import Toolkit.Decidable.Informative

import Toolkit.Data.Location
import Toolkit.Data.Whole
import Toolkit.Data.List.DeBruijn

import Ref



import Circuits.NetList.Types
import Circuits.NetList.Terms
import Circuits.NetList.AST

%default total

data Entry : (String,Ty) -> Type where
  MkEntry : (name : String)
         -> (type : Ty)
                 -> Entry (MkPair name type)

Env : List (String,Ty) -> Type
Env = Env (String,Ty) Entry


export
data Error = Mismatch Ty Ty
           | NotBound String
           | VectorExpected
           | PortExpected
           | OOB Nat Nat
           | ErrI String
           | Err FileContext Error
export
Show Error where
  show (Mismatch x y)
    = "Type Mismatch:\n\n"
      <+>
      unlines [unwords ["\tExpected:",show x], unwords ["\tGiven:", show y]]

  show (NotBound x)
    = unwords ["Undeclared variable:", x]

  show (VectorExpected)
    = "Vector Expected"

  show (PortExpected)
    = "Port Expected"

  show (ErrI msg)
    = "Internal Err: " <+> msg
  show (OOB x y)
    = unwords ["Out of Bounds:" , show x, "is not within", show y]

  show (Err x y) = unwords [show x, show y]

strip : {ctxt : List (String, Ty)}
     -> Elem (s,type) ctxt -> Elem type (map Builtin.snd ctxt)
strip Here = Here
strip (There x) = There (strip x)

public export
TyCheck : Type -> Type
TyCheck = Either Error

lift : Dec a -> Error -> TyCheck a
lift (Yes prf) _ = Right prf
lift (No contra) e = Left e

shouldCast : (flow,expected : Direction)
          -> (term : Term ctxt (TyPort (flow,type)))
                  -> Dec (Cast flow expected, Term ctxt (TyPort (expected,type)))
shouldCast flow expected term with (Cast.cast flow expected)
  shouldCast INOUT INPUT term | (Yes BI) = Yes (BI, Cast BI term)
  shouldCast INOUT OUTPUT term | (Yes BO) = Yes (BO, Cast BO term)
  shouldCast flow expected term | (No contra) = No (\(prf,t) => contra prf)

portCast : {type : DType}
      -> {flow : Direction}
      -> FileContext
      -> (expected : Direction)
      -> (term : Term ctxt (TyPort (flow,type)))
              -> TyCheck (Term ctxt (TyPort (expected,type)))

portCast {type} {flow = flow} fc exp term with (shouldCast flow exp term)
  portCast {type} {flow = flow} fc exp term | Yes (p,e)
    = Right e
  portCast {type} {flow = flow} fc exp term | No contra with (decEq flow exp)
    portCast {type} {flow = exp} fc exp term | No contra | (Yes Refl)
      = Right term
    portCast {type} {flow = flow} fc exp term | No contra | (No f)
      = Left (Err fc (Mismatch (TyPort (exp,type)) (TyPort (flow,type))))

checkPort : FileContext
         -> (expected : Direction)
         -> (term     : (ty ** Term ctxt ty))
                     -> TyCheck (Term ctxt (TyPort (expected,LOGIC)))

checkPort fc expected (MkDPair (TyPort (given,LOGIC)) term)
  = portCast fc expected term

checkPort fc expected (MkDPair (TyPort (given,ty)) term)
  = Left (Err fc (Mismatch (TyPort (expected,LOGIC)) (TyPort (given,ty))))

checkPort fc INPUT (MkDPair (TyChan LOGIC) term)
  = Right (Project READ term)

checkPort fc INPUT (MkDPair (TyChan y) term)
  = Left (Err fc (Mismatch (TyPort (INPUT,LOGIC)) (TyChan y)))

checkPort fc OUTPUT (MkDPair (TyChan LOGIC) term)
  = Right (Project WRITE term)

checkPort fc OUTPUT (MkDPair (TyChan y) term)
  = Left (Err fc (Mismatch (TyPort (OUTPUT,LOGIC)) (TyChan y)))

checkPort fc INOUT (MkDPair (TyChan y) term)
  = Left (Err fc (ErrI "INOUT CHAN not expected"))

checkPort fc expected (MkDPair type term)
  = Left (Err fc (Mismatch (TyPort (expected,LOGIC)) type))

typeCheck : {ctxt : List (String,Ty)}
         -> (curr : Env ctxt)
         -> (ast  : AST)
                  -> TyCheck (DPair Ty (Term (map Builtin.snd ctxt)))

typeCheck {ctxt} curr (Var x)
  = do (ty ** prf) <- lift (isIndex (get x) ctxt)
                           (Err (span x) (NotBound (get x)))

       pure (ty ** Var (strip prf))

typeCheck curr (Port fc flow ty n body)
  = do (TyUnit ** term) <- typeCheck (MkEntry (get n) (TyPort (flow,ty))::curr) body
         | (type ** _) => Left (Err fc (Mismatch TyUnit type))

       pure (_ ** Port flow ty term)

typeCheck curr (Wire fc ty n body)
  = do (TyUnit ** term) <- typeCheck (MkEntry (get n) (TyChan ty)::curr) body
         | (type ** _) => Left (Err fc (Mismatch TyUnit type))

       pure (_ ** Wire ty term)

typeCheck curr (GateDecl fc n g body)
  = do (TyGate ** gate) <- typeCheck curr g
         | (type ** _) => Left (Err fc (Mismatch TyGate type))

       (TyUnit ** term) <- typeCheck (MkEntry (get n) (TyGate)::curr) body
         | (type ** _) => Left (Err fc (Mismatch TyUnit type))

       pure (_ ** GateDecl gate term)

typeCheck curr (Mux fc o c l r)
  = do termO <- typeCheck curr o
       termC <- typeCheck curr c
       termL <- typeCheck curr l
       termR <- typeCheck curr r


       o' <- checkPort fc OUTPUT termO
       c' <- checkPort fc INPUT  termC
       l' <- checkPort fc INPUT  termL
       r' <- checkPort fc INPUT  termR

       pure (_ ** Mux o' c' l' r')

typeCheck curr (GateU fc k o i)
  = do termO <- typeCheck curr o
       termI <- typeCheck curr i

       o' <- checkPort fc OUTPUT termO
       i' <- checkPort fc INPUT  termI

       pure (_ ** GateU k o' i')

typeCheck curr (GateB fc k o l r)
  = do termO <- typeCheck curr o
       termL <- typeCheck curr l
       termR <- typeCheck curr r

       o' <- checkPort fc OUTPUT termO
       l' <- checkPort fc INPUT  termL
       r' <- checkPort fc INPUT  termR

       pure (_ ** GateB k o' l' r')

typeCheck curr (Index fc idx t)
  = do (TyPort (flow,BVECT (W (S n) ItIsSucc) type) ** term) <- typeCheck curr t
         | (type ** term)
             => Left (Err fc VectorExpected)

       case natToFin idx (S n) of
         Nothing => Left (OOB idx (S n))
         Just idx' => pure (_ ** Index term idx')

typeCheck curr (Stop x)
  = pure (_ ** Stop)

namespace Design
  export
  typeCheck : (ast : AST) -> TyCheck (Term Nil TyUnit)
  typeCheck ast with (typeCheck Nil ast)
    typeCheck ast | (Left x) = Left x
    typeCheck ast | (Right (MkDPair TyUnit term)) = Right term
    typeCheck ast | (Right (MkDPair ty snd)) = Left (Mismatch TyUnit ty)

  export
  typeCheckIO : (ast : AST) -> IO (TyCheck (Term Nil TyUnit))
  typeCheckIO ast = pure (typeCheck ast)

-- [ EOF ]
