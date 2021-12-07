module Circuits.Idealised

import Decidable.Equality

import Data.List.Elem
import Data.List.Quantifiers

import Circuits.Types
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
               -> (body     : Term ((Port (flow, datatype), FREE) :: old)
                                   Unit
                                   Nil)
                           -> Term old Unit Nil

      Wire : (datatype : DType)
          -> (body     : Term ((Port (OUTPUT,datatype), FREE)::(Port (INPUT,datatype), FREE)::old)
                              Unit
                              Nil)
                 -> Term old Unit Nil

      Mux : (output  : Term a (Port (OUTPUT, datatype)) b)
         -> (control : Term b (Port (INPUT,  LOGIC))    c)
         -> (inputA  : Term c (Port (INPUT,  datatype)) d)
         -> (inputB  : Term d (Port (INPUT,  datatype)) e)
                    -> Term a Gate e

      Dup : (outA  : Term a (Port (OUTPUT, datatype)) b)
         -> (outB  : Term b (Port (OUTPUT, datatype)) c)
         -> (input : Term c (Port (INPUT,  datatype)) d)
                  -> Term a Gate d


      Seq : Term a Gate b
         -> Term b Unit Nil
         -> Term a Unit Nil

      Not : (output : Term a (Port (OUTPUT, LOGIC)) b)
         -> (input  : Term b (Port (INPUT,  LOGIC)) c)
                   -> Term a Gate c

      Gate : (kind   : GateKind)
          -> (output : Term a (Port (OUTPUT, LOGIC)) b)
          -> (inputA : Term b (Port (INPUT,  LOGIC)) c)
          -> (inputB : Term c (Port (INPUT,  LOGIC)) d)
                    -> Term a Gate d

      IndexSingleton : (output : Term a (Port (OUTPUT,             datatype))  b)
                    -> (input  : Term b (Port (INPUT, (BVECT (S Z) datatype))) c)
                              -> Term a Gate c

      IndexEdge : (pivot : Nat)
               -> (idx   : Index size pivot free)
               -> (outu  : Term a (Port (OUTPUT,             datatype))  b)
               -> (outf  : Term b (Port (OUTPUT, (BVECT free datatype))) c)
               -> (input : Term c (Port (INPUT,  (BVECT size datatype))) d)
                        -> Term a Gate d

      IndexSplit : (pivot : Nat)
                -> (idx   : Index Z pivot size sizeA sizeB)
                -> (usedA : Term a (Port (OUTPUT,              datatype))  b)
                -> (freeA : Term b (Port (OUTPUT, (BVECT sizeA datatype))) c)
                -> (freeB : Term c (Port (OUTPUT, (BVECT sizeB datatype))) d)
                -> (input : Term d (Port (INPUT,  (BVECT size  datatype))) e)
                         -> Term a Gate e

      Stop : All Used old -> Term old Unit Nil

-- [ EOF ]
