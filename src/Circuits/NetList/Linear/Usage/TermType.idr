||| Declare the use of Terms
|||
||| Module    : TermType.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Predicates are defined in submodules.
module Circuits.NetList.Linear.Usage.TermType

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Decidable.Do
import Toolkit.Decidable.Equality.Indexed

import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Quantifiers
import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

import Circuits.NetList.Linear.Usage.DataType
import Circuits.NetList.Linear.Usage.DataType.Use.Full
import Circuits.NetList.Linear.Usage.DataType.Use.Partial

%default total

-- # [ Definitions ]

||| Usage of a term is dependent on the shape of the data it contains.
|||
||| Gates and Units are unrestricted.
public export
data Usage : Ty -> Type where
  TyPort : (u : Usage                type)
             -> Usage (TyPort (flow, type))

  TyChan : (ein  : Usage         type)
        -> (eout : Usage         type)
                -> Usage (TyChan type)

  TyGate : Usage TyGate
  TyUnit : Usage TyUnit

export
DecEq (TermType.Usage type) where
  decEq (TyPort u) (TyPort x)
    = decDo $ do Refl <- decEq u x `otherwise` (\Refl => Refl)
                 pure Refl

  decEq (TyChan a b) (TyChan x y)
    = decDo $ do Refl <- decEq a x `otherwise` (\Refl => Refl)
                 Refl <- decEq b y `otherwise` (\Refl => Refl)
                 pure Refl

  decEq TyGate TyGate = Yes Refl
  decEq TyUnit TyUnit = Yes Refl

export
DecEqIdx Ty Usage where
  decEq x y Refl with (Equality.decEq x y)
    decEq x x Refl | (Yes Refl)
      = Yes (Same Refl Refl)
    decEq x y Refl | (No no)
      = No (\(Same Refl Refl) => no Refl)


-- [ EOF ]
