module Circuits.NetList.Linear.Usage.TermType.Use.Port

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

%default total

namespace Full
  public export
  data Use : (type : Ty)
          -> (free : Usage type)
          -> (prfF : IsFree type free)
          -> (used : Usage type)
          -> (prfU : IsUsed type used)
                  -> Type
    where
      U : Use               type           free         pf          used         pu
       -> Use (TyPort (flow,type)) (TyPort free) (FreeP pf) (TyPort used) (UsedP pu)

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
  use (FreeP prf) with (use prf)
    use (FreeP prf) | (R x used result)
      = (R (TyPort x) (UsedP used) (U result))

namespace Partial

  public export
  data Use : (idx : Fin m)
          -> (type : Ty)
          -> (free : Usage type)
          -> (prfF : IsFreeAt idx type free)
          -> (used : Usage type)
          -> (prfU : IsUsedAt idx type used)
                  -> Type

    where
      U : Use idx                                         type            f          pF          u          pU
       -> Use idx (TyPort (flow,(BVECT (W (S n) ItIsSucc) type))) (TyPort f) (FreeAt pF) (TyPort u) (UsedAt pU)

  public export
  data Result : (idx : Fin m)
             -> (type : Ty)
             -> (free : Usage type)
             -> (prfF : IsFreeAt idx type free)
                     -> Type

    where
      R : (used  : Usage type)
       -> (prfU  : IsUsedAt idx type used)
       -> (holds : Use   idx type free prfF used prfU)
               -> Result idx type free prfF

  export
  use : (idx : Fin m)
     -> {type : Ty}
     -> {free : Usage type}
     -> (prfF : IsFreeAt idx type free)
             -> Result idx type free prfF
  use idx (FreeAt (FreeAt prf)) with (use idx prf)
    use idx (FreeAt (FreeAt prf)) | (R new prfU holds)
      = R (TyPort (Array new)) (UsedAt (UsedAt prfU)) (U (UA holds))



-- [ EOF ]
