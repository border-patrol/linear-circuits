||| Reason about used ports
|||
||| Module    : Used.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Port.Used

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
data IsUsed : (item : Item)
                   -> Type
  where
    Used : (prf : TermType.Port.IsUsed (TyPort (flow,type)) (TyPort usage))
               -> IsUsed (I (TyPort (flow,type)) (TyPort usage))

Uninhabited (IsUsed (I (TyChan ty) u)) where
  uninhabited (Used prf) impossible

Uninhabited (IsUsed (I TyGate u)) where
  uninhabited (Used prf) impossible

Uninhabited (IsUsed (I TyUnit u)) where
  uninhabited (Used prf) impossible

public export
data IsUsedNot : (item : Item)
                      -> Type
  where
    UsedNot : (prf : IsUsedNot type usage)
                  -> IsUsedNot (I type usage)

export
isUsed : (item : Item)
              -> DecInfo (IsUsedNot item)
                         (IsUsed    item)
isUsed (I t u) with (isUsed u)
  isUsed (I (TyPort (flow, type)) (TyPort u)) | (Yes (Used prf))
    = Yes (Used (Used prf))
  isUsed (I t u) | (No msg no)
    = No (UsedNot msg)
         (\(Used prf) => no prf)


-- [ EOF ]
