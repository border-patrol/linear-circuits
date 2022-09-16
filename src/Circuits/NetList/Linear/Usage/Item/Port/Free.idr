||| Reason about free ports
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Port.Free

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
data IsFree : (item : Item)
                   -> Type
  where
    Free : (prf : TermType.Port.IsFree (TyPort (flow,type)) (TyPort usage))
               -> IsFree (I (TyPort (flow,type)) (TyPort usage))

Uninhabited (IsFree (I (TyChan ty) u)) where
  uninhabited (Free prf) impossible

Uninhabited (IsFree (I TyGate u)) where
  uninhabited (Free prf) impossible

Uninhabited (IsFree (I TyUnit u)) where
  uninhabited (Free prf) impossible


public export
data IsFreeNot : (item : Item)
                      -> Type
  where
    FreeNot : (prf : IsFreeNot type usage)
                  -> IsFreeNot (I type usage)


export
isFree : (item : Item)
              -> DecInfo (IsFreeNot item)
                         (IsFree    item)
isFree (I t u) with (isFree u)
  isFree (I (TyPort (flow, type)) (TyPort u)) | (Yes (Free prf))
    = Yes (Free (Free prf))
  isFree (I t u) | (No msg no)
    = No (FreeNot msg)
         (\(Free prf) => no prf)


-- [ EOF ]
