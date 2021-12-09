module Circuits.Idealised.Types

import Decidable.Equality

import Data.List.Elem

%default total

public export
data GateKind = AND  | IOR  | XOR
              | ANDN | IORN | XORN | MERGE

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
  TyUnit : Ty
  TyPort : (Direction, DType) -> Ty

  TyGate : Ty

export
Show Ty where
  show TyUnit = "()"
  show (TyPort (d,t)) = concat ["TyPort(", show d, ",", show t, ")"]
  show TyGate = "TyGate"


Uninhabited (TyUnit = (TyPort x)) where
  uninhabited Refl impossible

Uninhabited (TyUnit = TyGate) where
  uninhabited Refl impossible

Uninhabited (TyPort x = TyGate) where
  uninhabited Refl impossible

export
DecEq Ty where
  decEq TyUnit TyUnit = Yes Refl
  decEq TyUnit (TyPort x) = No absurd
  decEq TyUnit TyGate = No absurd

  decEq (TyPort x) TyUnit = No (negEqSym absurd)
  decEq (TyPort x) (TyPort y) with (decEq x y)
    decEq (TyPort x) (TyPort x) | (Yes Refl)
      = Yes Refl
    decEq (TyPort x) (TyPort y) | (No contra)
      = No (\Refl => contra Refl)
  decEq (TyPort x) TyGate = No (absurd)

  decEq TyGate TyUnit = No (negEqSym absurd)
  decEq TyGate (TyPort x) = No (negEqSym absurd)
  decEq TyGate TyGate = Yes Refl


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