|||
|||
||| Module    : UsedAt.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Port.UsedAt

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

%default total

public export
data IsUsedAt : (is   : List Nat)
             -> (item : Item)
                     -> Type
  where
    UsedAt : {loc  : List Nat}
          -> (prf  : Port.IsUsedAt loc    type u)
                  -> IsUsedAt      loc (I type u)

public export
data IsUsedAtNot : (is   : List Nat)
                -> (item : Item)
                        -> Type
  where
    UsedAtNot : (prf  : Port.IsUsedAtNot loc    type u)
                     -> IsUsedAtNot      loc (I type u)


export
isUsedAt : (is   : List Nat)
        -> (item : Item)
                -> DecInfo (IsUsedAtNot is item)
                           (IsUsedAt    is item)
isUsedAt is (I type u) with (isUsedAt is u)
  isUsedAt is (I type u) | (Yes prf)
    = Yes (UsedAt prf)
  isUsedAt is (I type u) | (No msg no)
    = No (UsedAtNot msg)
         (\(UsedAt prf) => no prf)

-- [ EOF ]
