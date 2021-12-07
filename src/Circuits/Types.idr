module Circuits.Types

import Decidable.Equality

import Data.List.Elem

%default total

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

public export
data Direction = INPUT | OUTPUT

Uninhabited (INPUT = OUTPUT) where
  uninhabited Refl impossible

DecEq Direction where
  decEq INPUT INPUT   = Yes Refl
  decEq INPUT OUTPUT  = No absurd
  decEq OUTPUT INPUT  = No (negEqSym absurd)
  decEq OUTPUT OUTPUT = Yes Refl

export
Show Direction where
  show INPUT  = "input"
  show OUTPUT = "output"

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
data PortHasProperties : Direction -> DType -> (Direction, DType) -> Type
  where
    PortHas : PortHasProperties flow type (flow,type)

public export
data Ty : Type where
  Unit : Ty
  Port : (Direction, DType) -> Ty

  Gate : Ty

export
Show Ty where
  show Unit = "()"
  show (Port (d,t)) = concat ["Port(", show d, ",", show t, ")"]
  show Gate = "Gate"


Uninhabited (Unit = (Port x)) where
  uninhabited Refl impossible

Uninhabited (Unit = Gate) where
  uninhabited Refl impossible

Uninhabited (Port x = Gate) where
  uninhabited Refl impossible

export
DecEq Ty where
  decEq Unit Unit = Yes Refl
  decEq Unit (Port x) = No absurd
  decEq Unit Gate = No absurd

  decEq (Port x) Unit = No (negEqSym absurd)
  decEq (Port x) (Port y) with (decEq x y)
    decEq (Port x) (Port x) | (Yes Refl)
      = Yes Refl
    decEq (Port x) (Port y) | (No contra)
      = No (\Refl => contra Refl)
  decEq (Port x) Gate = No (absurd)

  decEq Gate Unit = No (negEqSym absurd)
  decEq Gate (Port x) = No (negEqSym absurd)
  decEq Gate Gate = Yes Refl


public export
data Used : (Ty, Usage) -> Type where
  IsUsed : Used (type, USED)

Uninhabited (Used (type,FREE)) where
  uninhabited IsUsed impossible

export
used : (p : (Ty,Usage)) -> Dec (Used p)
used (ty,USED) = Yes IsUsed
used (ty,FREE) = No absurd

public export
data Use : (old : List (Ty, Usage))
        -> (prf : Elem (type,FREE) old)
        -> (new : List (Ty, Usage))
        -> Type
  where
    H : Use ((type,FREE) :: rest)
            Here
            ((type,USED) :: rest)
    T : Use old later new
     -> Use ((type',usage')::old) (There later) ((type',usage')::new)

export
use : (ctxt : List (Ty, Usage))
   -> (prf : Elem (type, FREE) ctxt)
          -> (DPair (List (Ty, Usage))
                    (Use ctxt prf))
use ((type, FREE) :: xs) Here
  = (MkDPair ((type, USED) :: xs) H)
use ((y, z) :: xs) (There x) with (use xs x)
  use ((y, z) :: xs) (There x) | ((MkDPair fst snd))
    = (MkDPair ((y, z) :: fst) (T snd))

export
useAlt : {ctxt : List (Ty, Usage)}
      -> (prf : Elem (type, FREE) ctxt)
             -> (DPair (List (Ty, Usage))
                       (Use ctxt prf))
useAlt {ctxt = ((type, FREE) :: xs)} Here
  = MkDPair ((type, USED) :: xs) H
useAlt {ctxt = (y :: xs)} (There x) with (useAlt x)
  useAlt {ctxt = ((y, z) :: xs)} (There x) | (MkDPair fst snd) = MkDPair ((y, z) :: fst) (T snd)

-- [ EOF ]
