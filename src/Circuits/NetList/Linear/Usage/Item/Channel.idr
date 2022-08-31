||| Reason about useage of channel items.
|||
||| Module    : Channel.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Channel

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

import public Circuits.NetList.Linear.Usage.Item.Channel.CanProject as Circuits.NetList.Linear.Usage.Item.Channel
import public Circuits.NetList.Linear.Usage.Item.Channel.Use        as Circuits.NetList.Linear.Usage.Item.Channel

import public Circuits.NetList.Linear.Usage.Item.Channel.CanProjectAt as Circuits.NetList.Linear.Usage.Item.Channel
import public Circuits.NetList.Linear.Usage.Item.Channel.UseAt        as Circuits.NetList.Linear.Usage.Item.Channel


%default total


public export
data Init : (type : DType)
         -> (new  : Item)
                 -> Type
  where
    I : IsFree type u -> Init type (I (TyChan type) (TyChan u u))

export
init : (type : DType)
            -> DPair Item (Init type)
init type with (DataType.init type)
  init type | (MkDPair fst snd)
    = MkDPair (I (TyChan type) (TyChan fst fst)) (I snd)

-- [ EOF ]
