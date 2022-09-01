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
    FreePort : (prf : IsFreePort (I (TyPort (dir,type)) u) old)
            -> (use : UsePort    old prf new)
                   -> Term old (TyPort (dir,type)) new

    VarGate : (prf : IsGate (I TyGate TyGate) curr)
                  -> Term curr TyGate curr

    VarChan : (prf : IsChan (I (TyChan type) (TyChan uin uout)) curr)
                  -> Term curr (TyChan type) curr

    -- ## Structure
    Port : (flow : Direction)
        -> (type : DType)
        -> (urgh : Port.Init flow type item)
        -> (body : Term (item :: ctxt)
                        TyUnit
                        Nil)
                -> Term ctxt TyUnit Nil

    Wire : (type : DType)
        -> (urgh : Channel.Init type item)
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

    Assign : {type : DType}
          -> (o    : Term a (TyPort (OUTPUT,type)) b)
          -> (i    : Term b (TyPort (INPUT,type)) c)
          -> (body : Term d TyUnit e)
                  -> Term a TyUnit e
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
           -> (out  : Term a (TyPort (OUTPUT, type)) b)
           -> (inA  : Term b (TyPort (INPUT,  type)) c)
           -> (inB  : Term c (TyPort (INPUT,  type)) d)
                   -> Term a TyGate                  d

    -- ## Casting

    Cast : (cast : Cast INOUT flow)
        -> (port : Term a (TyPort (INOUT, type)) b)
                -> Term a (TyPort (flow,  type)) b

    -- ## Indexing

    Index : (idir : Index flow)
         -> (idx  : List Nat)
         -> (prf  : IsFreePortAt idx
                                 (I (TyPort (flow, BVECT (W (S n) ItIsSucc) type))
                                 u)
                                 old)
         -> (use  : UsePortAt idx old prf new)
         -> (prfT : HasTypeAt (BVECT (W (S n) ItIsSucc) type) idx typeo)
                -> Term old (TyPort (flow,typeo)) new

    -- ## Channel Projection

    Project : (how : Project dir)
           -> (prf : CanProject how (I (TyChan type) u) old)
           -> (use : UseChannel how old prf new)
                  -> Term old (TyPort (dir, type)) new

    ProjectAt : (how  : Project dir) -- TODO check
             -> (idx  : List Nat)
             -> (prf  : CanProjectAt how idx (I (TyChan (BVECT (W (S n) ItIsSucc)
                                                               type))
                                                        u) old)
             -> (use  : UseChannelAt how idx old prf new)
             -> (prfT : HasTypeAt (BVECT (W (S n) ItIsSucc) type) idx typeo)
                     -> Term old (TyPort (dir, typeo)) new


-- [ EOF ]
