module Circuits.NetList.Terms

import Decidable.Equality

import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.Quantifiers

import Data.String

import Data.Nat

import Toolkit.Data.DList
import Toolkit.Data.Whole

import Circuits.Common

import Circuits.NetList.Types

%default total

public export
data Term : (context : List Ty)
         -> (type    : Ty)
                    -> Type
  where
    Var : {type : Ty}
       -> (prf  : Elem type ctxt)
               -> Term ctxt type

    Port : (flow  : Direction)
        -> (dtype : DType)
        -> (body : Term (TyPort (flow, dtype)::ctxt) TyUnit)
                -> Term                        ctxt  TyUnit

    Wire : (type : DType)
        -> (body : Term (TyChan type :: ctxt) TyUnit)
                -> Term                 ctxt  TyUnit


    GateDecl : (g    : Term ctxt TyGate)
            -> (body : Term (TyGate::ctxt) TyUnit)
                    -> Term ctxt TyUnit

    Stop : Term ctxt TyUnit

    Assign : {type : DType}
          -> (i : Term ctxt (TyPort (INPUT,type)))
          -> (o : Term ctxt (TyPort (OUTPUT,type)))
          -> (body : Term ctxt TyUnit)
                  -> Term ctxt TyUnit

    Index : (idir : Index flow)
         -> (what : Term ctxt (TyPort (flow, BVECT (W (S n) ItIsSucc) type)))
         -> (idx  : Fin (S n))
         -> Term ctxt (TyPort (flow, type))

    Mux : (o   : Term ctxt (TyPort (OUTPUT, LOGIC)))
       -> (c   : Term ctxt (TyPort (INPUT,  LOGIC)))
       -> (l,r : Term ctxt (TyPort (INPUT,  LOGIC)))
              -> Term ctxt TyGate


    GateB : Binary.Kind
         -> (o   : Term ctxt (TyPort (OUTPUT, LOGIC)))
         -> (l,r : Term ctxt (TyPort (INPUT,  LOGIC)))
                -> Term ctxt TyGate

    GateU : Unary.Kind
         -> (o : Term ctxt (TyPort (OUTPUT, LOGIC)))
         -> (i : Term ctxt (TyPort (INPUT,  LOGIC)))
              -> Term ctxt TyGate

    Project : {type : DType}
           -> (how  : Project dir)
           -> (what : Term ctxt (TyChan type))
                   -> Term ctxt (TyPort (dir, type))

    Cast : {type : DType}
        -> (dir  : Cast INOUT flow)
        -> (what : Term ctxt (TyPort (INOUT, type)))
                -> Term ctxt (TyPort (flow,  type))

-- [ EOF ]
