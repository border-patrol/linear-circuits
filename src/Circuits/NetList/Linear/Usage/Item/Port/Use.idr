|||
|||
||| Module    : Use.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Port.Use

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

import public Circuits.NetList.Linear.Usage.Item.Port.Free
import public Circuits.NetList.Linear.Usage.Item.Port.Used

%default total

public export
data Use : (itemF : Item)
        -> (prfF  : IsFree itemF)
        -> (itemU : Item)
        -> (prfU  : IsUsed itemU)
                -> Type
  where

    U : (prf : TermType.Port.Use.Use (TyPort (fl,type))
                                     (TyPort f) pF
                                     (TyPort u) pU)
            -> Use (I (TyPort (fl,type)) (TyPort f)) (Free pF)
                   (I (TyPort (fl,type)) (TyPort u)) (Used pU)

public export
data Result : (itemF : Item)
           -> (prfF  : IsFree itemF)
                    -> Type
  where
    R : {itemU : Item}
     -> (prfU  : IsUsed itemU)
     -> (use   : Use itemF prfF itemU prfU)
              -> Result itemF prfF
export
use : {item : Item}
   -> (prf  : IsFree item)
           -> Result item prf
use (Free prf) with (use prf)
  use (Free prf) | (R (TyPort u) (Used y) x)
    = R (Used (Used y)) (U x)


-- [ EOF ]
