module Circuits.Idealised.Terms

import Decidable.Equality

import Data.List.Elem
import Data.List.Quantifiers

import Circuits.Idealised.Types
import Circuits.Split

%default total

namespace Circuits

  public export
  data Term : (old  : List (Ty, Usage))
           -> (type : Ty)
           -> (new  : List (Ty, Usage))
                   -> Type
    where
      Var : (prf : Elem (type, FREE) old)
         -> Use old prf new
         -> Term old type new

      NewSignal : (flow     : Direction)
               -> (datatype : DType)
               -> (body     : Term ((TyPort (flow, datatype), FREE) :: old)
                                   TyUnit
                                   Nil)
                           -> Term old TyUnit Nil

      Wire : (datatype : DType)
          -> (body     : Term ((TyPort (OUTPUT,datatype), FREE)::(TyPort (INPUT,datatype), FREE)::old)
                              TyUnit
                              Nil)
                 -> Term old TyUnit Nil

      Mux : (output  : Term a (TyPort (OUTPUT, datatype)) b)
         -> (control : Term b (TyPort (INPUT,  LOGIC))    c)
         -> (inputA  : Term c (TyPort (INPUT,  datatype)) d)
         -> (inputB  : Term d (TyPort (INPUT,  datatype)) e)
                    -> Term a TyGate e

      Dup : (outA  : Term a (TyPort (OUTPUT, datatype)) b)
         -> (outB  : Term b (TyPort (OUTPUT, datatype)) c)
         -> (input : Term c (TyPort (INPUT,  datatype)) d)
                  -> Term a TyGate d


      Seq : Term a TyGate b
         -> Term b TyUnit Nil
         -> Term a TyUnit Nil

      Not : (output : Term a (TyPort (OUTPUT, LOGIC)) b)
         -> (input  : Term b (TyPort (INPUT,  LOGIC)) c)
                   -> Term a TyGate c

      Gate : (kind   : GateKind)
          -> (output : Term a (TyPort (OUTPUT, LOGIC)) b)
          -> (inputA : Term b (TyPort (INPUT,  LOGIC)) c)
          -> (inputB : Term c (TyPort (INPUT,  LOGIC)) d)
                    -> Term a TyGate d

      IndexSingleton : (output : Term a (TyPort (OUTPUT,             datatype))  b)
                    -> (input  : Term b (TyPort (INPUT, (BVECT (S Z) datatype))) c)
                              -> Term a TyGate c

      IndexEdge : (pivot : Nat)
               -> (idx   : Index size pivot free)
               -> (outu  : Term a (TyPort (OUTPUT,             datatype))  b)
               -> (outf  : Term b (TyPort (OUTPUT, (BVECT free datatype))) c)
               -> (input : Term c (TyPort (INPUT,  (BVECT size datatype))) d)
                        -> Term a TyGate d

      IndexSplit : (pivot : Nat)
                -> (idx   : Index Z pivot size sizeA sizeB)
                -> (usedA : Term a (TyPort (OUTPUT,              datatype))  b)
                -> (freeA : Term b (TyPort (OUTPUT, (BVECT sizeA datatype))) c)
                -> (freeB : Term c (TyPort (OUTPUT, (BVECT sizeB datatype))) d)
                -> (input : Term d (TyPort (INPUT,  (BVECT size  datatype))) e)
                         -> Term a TyGate e

      Stop : All Used old -> Term old TyUnit Nil

-- [ EOF ]
