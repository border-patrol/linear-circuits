module Circuits.Idealised

import Decidable.Equality

import Data.List.Elem
import Data.List.Quantifiers

import Circuits.Types

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

      Seq : Term a Gate b
         -> Term b Unit Nil
         -> Term a Unit Nil

      Not : (output : Term a (Port (OUTPUT, datatype)) b)
         -> (input  : Term b (Port (INPUT,  datatype)) c)
                   -> Term a Gate c

      Gate : (output : Term a (Port (OUTPUT, datatype)) b)
          -> (inputA : Term b (Port (INPUT,  datatype)) c)
          -> (inputB : Term c (Port (INPUT,  datatype)) d)
                    -> Term a Gate d

      Stop : All Used old -> Term old Unit Nil

-- [ EOF ]
