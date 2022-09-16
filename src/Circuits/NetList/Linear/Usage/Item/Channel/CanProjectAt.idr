||| Reason about useage of channel items.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Channel.CanProjectAt

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String
import Data.Singleton

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

import Circuits.NetList.Linear.Usage.TermType.Channel
import Circuits.NetList.Linear.Usage.TermType.Channel.Use

%default total

public export
data CanProjectAt : (how  : Project dir)
                 -> (idx  : List Nat)
                 -> (item : Item)
                         -> Type
  where
    ProjectAt : (prf : CanProjectAt how idx    (TyChan type) (TyChan ein eout))
                    -> CanProjectAt how idx (I (TyChan type) (TyChan ein eout))

public export
data CanProjectAtNot : (how  : Project dir)
                    -> (idx  : List Nat)
                    -> (item : Item)
                            -> Type
  where
    ProjectAtNot : (prf : CanProjectAtNot how idx    type u)
                       -> CanProjectAtNot how idx (I type u)

export
canProjectAt : (how  : Project dir)
            -> (idx  : List Nat)
            -> (item : Item)
                    -> DecInfo (CanProjectAtNot how idx item)
                               (CanProjectAt    how idx item)
canProjectAt how idx (I t u) with (canProjectAt how idx u)
  canProjectAt WRITE idx (I (TyChan type) (TyChan ein eout)) | (Yes (ProjectAtWrite prf))
    = Yes (ProjectAt (ProjectAtWrite prf))
  canProjectAt READ idx (I (TyChan type) (TyChan ein eout)) | (Yes (ProjectAtRead prf))
    = Yes (ProjectAt (ProjectAtRead prf))
  canProjectAt how idx (I t u) | (No msg no)
    = No (ProjectAtNot msg)
         (\(ProjectAt prf) => no prf)


-- [ EOF ]
