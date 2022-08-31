||| Usage definitions for datatypes.
|||
||| Module    : DataType.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.DataType.Def

import Decidable.Equality
import Toolkit.Decidable.Equality.Indexed

import Data.Vect

import Toolkit.Data.Fin
import Toolkit.Data.Whole

import Circuits.Common
import Circuits.NetList.Types

%default total

||| Datatypes & their usages.
public export
data Usage : (datatype : DType)
                      -> Type
  where
    ||| Wires have a single usage.
    Logic : (u : Usage)
              -> Usage LOGIC

    ||| Bitvectors have a usage per element.
    Array : (us : Vect            (S n)           (Usage type))
               -> Usage (BVECT (W (S n) ItIsSucc)        type)


export
DecEq (Usage type) where
  decEq (Logic u) (Logic x) with (decEq u x)
    decEq (Logic u) (Logic u) | (Yes Refl)
      = Yes Refl

    decEq (Logic u) (Logic x) | (No no)
      = No (\Refl => no Refl)

  decEq (Array us) (Array vs) with (Equality.decEq us vs)
    decEq (Array us) (Array us) | (Yes Refl)
      = Yes Refl

    decEq (Array us) (Array vs) | (No no)
      = No (\Refl => no Refl)

export
DecEqIdx DType Usage where
  decEq x y Refl with (Equality.decEq x y)
    decEq x x Refl | (Yes Refl) = Yes (Same Refl Refl)
    decEq x y Refl | (No no)
      = No (\(Same Refl Refl) => no Refl)

public export
data SafeIndex : (n   : Nat)
              -> (us  : Vect m (Usage type))
                     -> Type
  where
    SI : {ms : Vect m (Usage type)} -> (f : Fin m) -> NatToFin n m f -> SafeIndex n ms

export
safeIndex : {m  : Nat}
         -> (n  : Nat)
         -> (us : Vect m (Usage type))
               -> Dec (SafeIndex n us)
safeIndex n {m} us with (Safe.natToFin n m)
  safeIndex n {m = m} us | (Yes ((fst ** snd))) = Yes (SI fst snd)
  safeIndex n {m = m} us | (No contra) = No (\(SI fst prf) => contra (fst ** prf))

-- [ EOF ]
