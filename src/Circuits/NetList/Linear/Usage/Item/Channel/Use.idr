||| Reason about useage of channel items.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Channel.Use

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

import Circuits.NetList.Linear.Usage.Item.Channel.CanProject

%default total


public export
data Use : (how  : Project dir)
        -> (old  : Item)
        -> (prf  : CanProject how old)
        -> (new  : Item)
        -> (prfN : Singleton new) -- A cheat for later own.
                -> Type
  where
    U : (use : Use how    (TyChan type) (TyChan i o)           prf                   (TyChan i' o'))
            -> Use how (I (TyChan type) (TyChan i o)) (Project prf) (I (TyChan type) (TyChan i' o')) (Val (I (TyChan type) (TyChan i' o')))

public export
data Result : (how : Project dir)
           -> (old : Item)
           -> (prf : CanProject how old)
                  -> Type
  where
   R : {new : Item}
      -> (use : Use how old prf new (Val new))
           -> Result how old prf

export
use : {old : Item}
   -> (prf : CanProject how old)
          -> Result how old prf
use {old = (I (TyChan type) (TyChan ein eout))} (Project prf) with (use prf)
  use {old = (I (TyChan type) (TyChan ein eout))} (Project (ProjectWrite free)) | (R (TyChan newU eout) (IsWrite x))
    = R (U (IsWrite x))
  use {old = (I (TyChan type) (TyChan ein eout))} (Project (ProjectRead free)) | (R (TyChan ein newU) (IsRead x))
    = R (U (IsRead x))

-- [ EOF ]
