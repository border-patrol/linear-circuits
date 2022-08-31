||| Reason about useage of port items.
|||
||| Module    : Item.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Port

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

import public Circuits.NetList.Linear.Usage.Item.Port.Free as Circuits.NetList.Linear.Usage.Item.Port
import public Circuits.NetList.Linear.Usage.Item.Port.Used as Circuits.NetList.Linear.Usage.Item.Port
import public Circuits.NetList.Linear.Usage.Item.Port.Use  as Circuits.NetList.Linear.Usage.Item.Port

import public Circuits.NetList.Linear.Usage.Item.Port.FreeAt as Circuits.NetList.Linear.Usage.Item.Port
import public Circuits.NetList.Linear.Usage.Item.Port.UsedAt as Circuits.NetList.Linear.Usage.Item.Port
import public Circuits.NetList.Linear.Usage.Item.Port.UseAt  as Circuits.NetList.Linear.Usage.Item.Port

%default total

public export
data Init : (flow : Direction)
         -> (type : DType)
         -> (new  : Item)
                 -> Type
  where
    I : IsFree type u -> Init flow type (I (TyPort (flow,type)) (TyPort u))

export
init : (flow : Direction)
    -> (type : DType)
            -> DPair Item (Init flow type)
init flow type with (init type)
  init flow type | (MkDPair fst snd)
    = MkDPair (I (TyPort (flow, type)) (TyPort fst)) (I snd)

-- [ EOF ]
