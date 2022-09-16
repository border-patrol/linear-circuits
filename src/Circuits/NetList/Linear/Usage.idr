||| Usage predicates over types, datatypes, and contexts.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage

import Decidable.Equality

import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Extra

import Circuits.Common

import Circuits.NetList.Types

import public Circuits.NetList.Linear.Context

import public Circuits.NetList.Linear.Usage.DataType
import public Circuits.NetList.Linear.Usage.DataType.Use.Full
import public Circuits.NetList.Linear.Usage.DataType.Use.Partial

import public Circuits.NetList.Linear.Usage.TermType
import public Circuits.NetList.Linear.Usage.TermType.Port
import public Circuits.NetList.Linear.Usage.TermType.Port.Use
import public Circuits.NetList.Linear.Usage.TermType.Channel
import public Circuits.NetList.Linear.Usage.TermType.Channel.Use

import public Circuits.NetList.Linear.Usage.Item.Port
import public Circuits.NetList.Linear.Usage.Item.Channel
import public Circuits.NetList.Linear.Usage.Context

%default total


-- [ EOF ]
