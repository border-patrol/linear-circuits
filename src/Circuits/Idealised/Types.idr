module Circuits.Idealised.Types

import Decidable.Equality

import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Renaming

import public Circuits.Common

%default total

public export
data GateKind = AND  | IOR  | XOR
              | ANDN | IORN | XORN | JOIN

public export
data Direction = INPUT | OUTPUT

Uninhabited (INPUT = OUTPUT) where
  uninhabited Refl impossible

DecEq Direction where
  decEq INPUT INPUT   = Yes Refl
  decEq INPUT OUTPUT  = No absurd
  decEq OUTPUT INPUT  = No (negEqSym absurd)
  decEq OUTPUT OUTPUT = Yes Refl

public export
data PortHasProperties : Direction -> DType -> (Direction, DType) -> Type
  where
    PortHas : PortHasProperties flow type (flow,type)

public export
data Ty : Type where
  TyUnit : Ty
  TyPort : (Direction, DType) -> Ty

  TyGate : Ty

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

export
Uninhabited (Used (type,FREE)) where
  uninhabited IsUsed impossible

export
used : (p : (Ty,Usage)) -> Dec (Used p)
used (ty,USED) = Yes IsUsed
used (ty,FREE) = No absurd

public export
data Use : (old : List (Ty, Usage))
        -> (prf : IsVar old (type,FREE))
        -> (new : List (Ty, Usage))
        -> Type
  where
    H : Use ((type,FREE) :: rest)
            (V Z Here)
            ((type,USED) :: rest)

    T : Use old (V n later) new
     -> Use ((type',usage')::old)
            (V (S n) (There later))
            ((type',usage')::new)

Uninhabited (IsVar Nil type) where
  uninhabited (V _ Here) impossible
  uninhabited (V _ (There later)) impossible

Uninhabited (AtIndex type Nil pos) where
  uninhabited Here impossible
  uninhabited (There later) impossible


export
use : {ctxt : List (Ty, Usage)}
   -> (prf  : IsVar ctxt (type, FREE))
           -> (DPair (List (Ty, Usage))
                     (Use ctxt prf))
use {ctxt = Nil} (V _ Here) impossible
use {ctxt = ((type, FREE) :: xs)} (V 0 Here)
  = MkDPair ((type, USED) :: xs) H

use {ctxt = (y :: rest)} (V (S idx) (There later)) with (use (V idx later))
  use {ctxt = ((t,u) :: rest)} (V (S idx) (There later)) | (MkDPair fst snd)
    = MkDPair ((t,u) :: fst) (T snd)

-- [ EOF ]
