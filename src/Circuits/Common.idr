module Circuits.Common

import Decidable.Equality

%default total

public export
data DType = LOGIC | BVECT Nat DType

Uninhabited (LOGIC = BVECT n k) where
  uninhabited Refl impossible

export
Show DType where
  show LOGIC = "logic"
  show (BVECT n type) = show type <+> concat ["[", show n, "]"]

export
DecEq DType where
  decEq LOGIC LOGIC = Yes Refl
  decEq LOGIC (BVECT k x) = No absurd

  decEq (BVECT k x) LOGIC = No (negEqSym absurd)
  decEq (BVECT k x) (BVECT j y) with (decEq k j)
    decEq (BVECT k x) (BVECT k y) | (Yes Refl) with (decEq x y)
      decEq (BVECT k x) (BVECT k x) | (Yes Refl) | (Yes Refl)
        = Yes Refl
      decEq (BVECT k x) (BVECT k y) | (Yes Refl) | (No contra)
        = No (\Refl => contra Refl)

    decEq (BVECT k x) (BVECT j y) | (No contra)
      = No (\Refl => contra Refl)


public export
data Usage = USED | FREE

Uninhabited (USED = FREE) where
  uninhabited Refl impossible

export
Show Usage where
  show USED = "Used"
  show FREE = "Free"

export
DecEq Usage where
  decEq USED USED = Yes Refl
  decEq USED FREE = No absurd
  decEq FREE USED = No (negEqSym absurd)
  decEq FREE FREE = Yes Refl

-- [ EOF ]
