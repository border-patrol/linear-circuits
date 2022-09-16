|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.Common

import System

import Decidable.Equality

import Data.Nat
import Toolkit.Data.Whole
import Toolkit.Data.Vect.Extra

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
data HasTypeAt : (type  : DType)
              -> (idx   : List Nat)
              -> (typeO : DType)
                       -> Type
  where
    Here  : HasTypeAt (BVECT w type) [idx] type
    There : HasTypeAt          type      (i'::is) typeo
         -> HasTypeAt (BVECT w type) (i:: i'::is) typeo

Uninhabited (HasTypeAt LOGIC ns type) where
  uninhabited Here impossible
  uninhabited (There x) impossible

Uninhabited (HasTypeAt type Nil typeo) where
  uninhabited Here impossible
  uninhabited (There x) impossible

public export
data HasTypeAtResult : (type : DType) -> (idx : List Nat) -> Type
  where
    R : {type,typeo : DType} -> HasTypeAt type idx typeo -> HasTypeAtResult type idx

export
hasTypeAt : (type : DType)
         -> (idx  : List Nat)
                 -> Dec (HasTypeAtResult type idx)
hasTypeAt type []
  = No (\(R prf) => absurd prf)

hasTypeAt LOGIC (x :: xs)
  = No (\(R prf) => absurd prf)

hasTypeAt (BVECT w type) (x :: [])
  = Yes (R Here)
hasTypeAt (BVECT w type) (x :: (y :: xs)) with (hasTypeAt type (y::xs))
  hasTypeAt (BVECT w type) (x :: (y :: xs)) | (Yes (R prf))
    = Yes (R (There prf))
  hasTypeAt (BVECT w type) (x :: (y :: xs)) | (No no)
    = No (\(R (There prf)) => no (R prf))

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
