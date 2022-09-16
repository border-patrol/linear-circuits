||| Reason about free ports
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Port.FreeAt

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Decidable.Informative
import Toolkit.Data.Fin
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
data IsFreeAt : (is   : List Nat)
             -> (item : Item)
                     -> Type
  where
    FreeAt : {loc  : List Nat}
          -> (prf  : Port.IsFreeAt loc    type u)
                  -> IsFreeAt      loc (I type u)

public export
data IsFreeAtNot : (is   : List Nat)
                -> (item : Item)
                        -> Type
  where
    FreeAtNot : (prf  : Port.IsFreeAtNot loc    type u)
                     -> IsFreeAtNot      loc (I type u)


export
isFreeAt : (is   : List Nat)
        -> (item : Item)
                -> DecInfo (IsFreeAtNot is item)
                           (IsFreeAt    is item)
isFreeAt is (I type u) with (isFreeAt is u)
  isFreeAt is (I type u) | (Yes prf)
    = Yes (FreeAt prf)
  isFreeAt is (I type u) | (No msg no)
    = No (FreeAtNot msg)
         (\(FreeAt prf) => no prf)

-- [ EOF ]
