module Circuits.Common

import System

import Decidable.Equality

import Data.Nat
import Toolkit.Data.Whole

%default total

export
processArgs : List String -> IO String
processArgs [exe,fname] = pure fname
processArgs _
  = do putStrLn "Exactly one file at a time."
       exitFailure

public export
data DType = LOGIC | BVECT Whole DType

public export
size : DType -> Nat
size LOGIC = (S Z)
size (BVECT (W (S n) ItIsSucc) type)
  = mult (S n) (size type)


Uninhabited (LOGIC = BVECT n k) where
  uninhabited Refl impossible

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
DecEq Usage where
  decEq USED USED = Yes Refl
  decEq USED FREE = No absurd
  decEq FREE USED = No (negEqSym absurd)
  decEq FREE FREE = Yes Refl

-- [ EOF ]
