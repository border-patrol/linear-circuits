||| Predicates reasoning about using datatypes.
|||
||| Module    : DataType.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.DataType

import Decidable.Equality

import Data.Nat
import Data.List.Elem

import Data.Singleton

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Decidable.Equality.Indexed

import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import public Toolkit.Data.Vect.Quantifiers

import Circuits.Common

import Circuits.NetList.Types

import public Circuits.NetList.Linear.Usage.DataType.Def    as Circuits.NetList.Linear.Usage.DataType

-- [ NOTE ] We can make make things dry for Free/Used & FreeAt/UsedAt
-- by each using a singular structure parameterised over a
-- predicate... Something for later.
--
import public Circuits.NetList.Linear.Usage.DataType.Free   as Circuits.NetList.Linear.Usage.DataType
import public Circuits.NetList.Linear.Usage.DataType.FreeAt as Circuits.NetList.Linear.Usage.DataType

import public Circuits.NetList.Linear.Usage.DataType.Used   as Circuits.NetList.Linear.Usage.DataType
import public Circuits.NetList.Linear.Usage.DataType.UsedAt as Circuits.NetList.Linear.Usage.DataType

%default total

-- # [ Type-Driven Usage Initialisation ]

mutual

  export
  init : (type : DType) -> DPair (Usage type) (IsFree type)
  init LOGIC
    = MkDPair (Logic FREE) FreeL

  init (BVECT (W (S n) ItIsSucc) type) with (init type)
    init (BVECT (W (S n) ItIsSucc) type) | (MkDPair u prf) with (init (S n) u prf)
      init (BVECT (W (S n) ItIsSucc) type) | (MkDPair u prf) | (MkDPair os pU)
        = MkDPair (Array os) (FreeA pU)

  namespace Vect
    export
    init : (n   : Nat)
        -> (u   : Usage type)
        -> (prf : IsFree type u)
               -> DPair (Vect n (Usage type)) (All (IsFree type))
    init Z _ _ = MkDPair [] []
    init (S k) u prf with (init k u prf)
      init (S k) u prf | (MkDPair fst snd)
        = MkDPair (u :: fst) (prf :: snd)

-- [ EOF ]
