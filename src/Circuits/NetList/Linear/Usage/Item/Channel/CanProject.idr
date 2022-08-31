||| Reason about useage of channel items.
|||
||| Module    : Channel.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Channel.CanProject

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
data CanProject : (how  : Project dir)
               -> (item : Item)
                       -> Type
  where
    Project : (prf : CanProject how    (TyChan type) (TyChan ein eout))
                  -> CanProject how (I (TyChan type) (TyChan ein eout))

public export
data CanProjectNot : (how  : Project dir)
                  -> (item : Item)
                          -> Type
  where
    ProjectNot : (prf : CanProjectNot how    type u)
                     -> CanProjectNot how (I type u)

export
canProject : (how  : Project dir)
          -> (item : Item)
                  -> DecInfo (CanProjectNot how item)
                             (CanProject    how item)
canProject how (I t u) with (canProject how u)
  canProject WRITE (I (TyChan type) (TyChan ein eout)) | (Yes (ProjectWrite prf))
    = Yes (Project (ProjectWrite prf))
  canProject READ (I (TyChan type) (TyChan ein eout)) | (Yes (ProjectRead prf))
    = Yes (Project (ProjectRead prf))
  canProject how (I t u) | (No msg no)
    = No (ProjectNot msg)
         (\(Project prf) => no prf)


-- [ EOF ]
