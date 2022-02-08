module Circuits.NetList.Linear.Terms

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Data.Whole

import Circuits.Common

import Circuits.NetList.Types
import Circuits.NetList.Linear.Usage


%default total

public export
data Term : (start : List Item)
         -> (item  : Ty)
         -> (next  : List Item)
                   -> Type
  where
    -- ## Vars
    VarPort : (prf : IsFreePort (I (TyPort (flow,type)) u) ctxt_a)
           -> (use : UsePort ctxt_a prf ctxt_b)
                  -> Term ctxt_a
                          (TyPort (flow,type))
                          ctxt_b

    -- ## Structure

    Port : (flow : Direction)
        -> (type : DType)
        -> (urgh : FreePort flow type item)
        -> (body : Term (item :: ctxt)
                        TyUnit
                        Nil)
                -> Term ctxt TyUnit Nil

    Wire : (type : DType)
        -> (urgh : FreeChan type item)
        -> (body : Term (item :: ctxt)
                        TyUnit
                        Nil)
                -> Term ctxt TyUnit Nil

    Gate : (gate : Term this TyGate that)
        -> (body : Term (I TyGate TyGate :: that)
                        TyUnit
                        Nil)
                -> Term this TyUnit Nil

    Stop : (prf : All CanStop ctxt)
               -> Term ctxt TyUnit Nil

    -- ## Gates

    Mux : (out  : Term a (TyPort (OUTPUT, LOGIC)) b)
       -> (ctrl : Term b (TyPort (INPUT,  LOGIC)) c)
       -> (inA  : Term c (TyPort (INPUT,  LOGIC)) d)
       -> (inB  : Term d (TyPort (INPUT,  LOGIC)) e)
               -> Term a  TyGate                  e

    GateU : (kind : Unary.Kind)
         -> (out  : Term a (TyPort (OUTPUT, LOGIC)) b)
         -> (inA  : Term b (TyPort (INPUT,  LOGIC)) c)
                 -> Term a TyGate                   c

    GateB : (kind : Binary.Kind)
         -> (out  : Term a (TyPort (OUTPUT, LOGIC)) b)
         -> (inA  : Term b (TyPort (INPUT,  LOGIC)) c)
         -> (inB  : Term c (TyPort (INPUT,  LOGIC)) d)
                 -> Term a TyGate                   d

    -- ## For linearity

    Split : (outA : Term a (TyPort (OUTPUT,LOGIC)) b)
         -> (outB : Term b (TyPort (OUTPUT,LOGIC)) c)
         -> (inp  : Term c (TyPort (INPUT, LOGIC)) d)
                 -> Term a TyGate                  d

    Collect : {type : DType}
           -> (out  : Term a (TyPort (OUTPUT,BVECT (W (S (S Z)) ItIsSucc) type)) b)
           -> (inA  : Term b (TyPort (OUTPUT,type)) c)
           -> (inB  : Term c (TyPort (INPUT, type)) d)
                   -> Term a TyGate                  d

    -- ## Port Manipulation & Channel Projection

    Cast : (cast : Cast INOUT flow)
        -> (port : Term a (TyPort (INOUT, type)) b)
                -> Term a (TyPort (flow,  type)) b

    Project : (how : Project dir)
           -> (prf : IsFreeChannel how (I (TyChan type) (TyChan ein eout)) this)
           -> (use : ProjectChannel how this prf that)
                  -> Term this (TyPort (dir,type)) that

    Index : (idir : Index flow)
         -> (idx : Fin a)
         -> (prf : CanIndexPort idx (I (TyPort (flow, BVECT (W (S n) ItIsSucc) type)) u) this)
         -> (use : IndexPort idx this prf that)
                -> Term this (TyPort (flow,type)) that

-- [ EOF ]
