||| Using Ports
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.TermType.Port.Use

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

import Circuits.NetList.Linear.Usage.DataType

import Circuits.NetList.Linear.Usage.DataType.Use.Full
import Circuits.NetList.Linear.Usage.DataType.Use.Partial

import Circuits.NetList.Linear.Usage.TermType
import Circuits.NetList.Linear.Usage.TermType.Port

%default total


public export
data Use : (type : Ty)
        -> (free : Usage type)
        -> (prfF : IsFree type free)
        -> (used : Usage type)
        -> (prfU : IsUsed type used)
                -> Type
  where
    U : Use               type           free        pf          used        pu
     -> Use (TyPort (flow,type)) (TyPort free) (Free pf) (TyPort used) (Used pu)

namespace Full
  public export
  data Result : (free : Usage  (TyPort (f,dtype)))
             -> (prfF : IsFree (TyPort (f,dtype)) free)
                     -> Type
    where
     R : (used : Usage  (TyPort (f,dtype)))
      -> (prfU : IsUsed (TyPort (f,dtype)) used)
      -> (prf  : Use    (TyPort (f,dtype)) free prfF used prfU)
              -> Result free prfF

export
use : {dtype : DType}
   -> {free : Usage  (TyPort (f,dtype))}
   -> (prfF : IsFree (TyPort (f,dtype)) free)
           -> Result free prfF
use (Free prf) with (use prf)
  use (Free prf) | (R x used result)
    = (R (TyPort x) (Used used) (U result))


public export
data UseAt : (idx  : List Nat)
          -> (type : Ty)
          -> (free : Usage type)
          -> (prfF : IsFreeAt idx type free)
          -> (used : Usage type)
          -> (prfU : IsUsedAt idx type used)
                  -> Type

  where
    UAt : UseAt idx               (BVECT (W (S n) ItIsSucc) type)           f          pF          u          pU
       -> UseAt idx (TyPort (flow,(BVECT (W (S n) ItIsSucc) type))) (TyPort f) (FreeAt pF) (TyPort u) (UsedAt pU)

namespace Partial
  public export
  data Result : (idx  : List Nat)
             -> (type : Ty)
             -> (free : Usage type)
             -> (prfF : IsFreeAt idx type free)
                     -> Type

    where
      R : {idx   : List Nat}
       -> {prfF  : IsFreeAt idx type free}
       -> (used  : Usage type)
       -> (prfU  : IsUsedAt idx type used)
       -> (holds : UseAt  idx type free prfF used prfU)
                -> Result idx type free prfF

export
useAt : {idx  : List Nat}
     -> {type : Ty}
     -> {free : Usage type}
     -> (prfF : IsFreeAt idx type free)
             -> Result idx type free prfF
useAt (FreeAt prf) with (prf)
  useAt (FreeAt prf) | prf' with (useAt _ prf')
    useAt (FreeAt prf) | prf' | (R new prfU holds)
      = R (TyPort new) (UsedAt prfU) (UAt holds)

-- [ EOF ]
