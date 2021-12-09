module Circuits.NetList.Terms

import Decidable.Equality

import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Data.DList

import Circuits.Common

import Circuits.NetList.Types

%default total

public export
data Term : (context : List Ty)
         -> (type    : Ty)
                    -> Type
  where
    Var : Elem type ctxt
       -> Term ctxt type

    Port : (flow : Direction)
        -> (type : DType)
        -> (body : Term (TyPort (flow, type)::ctxt) TyUnit)
                -> Term                       ctxt  TyUnit

    Wire : (type : DType)
        -> (body : Term (TyChan type :: ctxt) TyUnit)
                -> Term                 ctxt  TyUnit

    Stop : Term ctxt TyUnit

    Index : Term ctxt (TyPort (flow, BVECT n type))
         -> Fin n
         -> Term ctxt (TyPort (flow, type))

    GateB : Binary.Kind
         -> (o   : Term ctxt (TyPort (OUTPUT, LOGIC)))
         -> (l,r : Term ctxt (TyPort (INPUT,  LOGIC)))
                -> Term ctxt TyGate

    GateU : Unary.Kind
         -> (o : Term ctxt (TyPort (OUTPUT, LOGIC)))
         -> (i : Term ctxt (TyPort (INPUT,  LOGIC)))
              -> Term ctxt TyGate

    GateDecl : (g    : Term ctxt TyGate)
            -> (body : Term (TyGate::ctxt) TyUnit)
                    -> Term ctxt TyUnit

    Project : Project dir
           -> Term ctxt (TyChan type)
           -> Term ctxt (TyPort (dir, type))

    Cast : Cast INOUT flow
        -> Term ctxt (TyPort (INOUT, type))
        -> Term ctxt (TyPort (flow,  type))

-- [ EOF ]
