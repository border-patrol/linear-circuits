|||
|||
||| Module    : UseAt.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Port.UseAt

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Decidable.Informative
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
import Circuits.NetList.Linear.Context

import Circuits.NetList.Linear.Usage.TermType.Port
import Circuits.NetList.Linear.Usage.TermType.Port.Use

import Circuits.NetList.Linear.Usage.Item.Port.FreeAt
import Circuits.NetList.Linear.Usage.Item.Port.UsedAt

%default total


public export
data UseAt : (idx  : List Nat)
          -> (old  : Item)
          -> (free : IsFreeAt idx old)
          -> (new  : Item)
          -> (used : IsUsedAt idx new)
                  -> Type
  where
    UAt : (prf : UseAt idx    (TyPort (f, BVECT (W (S n) ItIsSucc) type)) (TyPort uF)          pF  (TyPort uU)          pU)
              -> UseAt idx (I (TyPort (f, BVECT (W (S n) ItIsSucc) type)) (TyPort uF)) (FreeAt pF)
                           (I (TyPort (f, BVECT (W (S n) ItIsSucc) type))                          (TyPort uU)) (UsedAt pU)


public export
data Result : (idx  : List Nat)
           -> (old  : Item)
           -> (free : IsFreeAt idx old)
                    -> Type
  where
    R : {idx  : List Nat}
     -> {old  : Item}
     -> {free : IsFreeAt idx old}
     -> (new  : Item)
     -> (used : IsUsedAt idx new)
     -> (uAt  : UseAt  idx old free new used)
             -> Result idx old free

export
useAt : {idx  : List Nat}
     -> {old  : Item}
     -> (free : IsFreeAt idx old)
             -> Result   idx old free
useAt (FreeAt prf) with (useAt prf)
  useAt (FreeAt (FreeAt pF)) | (R (TyPort us) (UsedAt x) (UAt y))
    = R (I _ (TyPort us)) (UsedAt (UsedAt x)) (UAt (UAt y))

-- [ EOF ]
