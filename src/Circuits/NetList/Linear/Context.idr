|||
|||
||| Module    : Linear/Context.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Context

import public Data.Singleton

import public Decidable.Equality

import public Circuits.NetList.Types
import public Circuits.NetList.Linear.Usage.TermType

import public Toolkit.Decidable.Equality.Indexed

%default total

public export
record Item where
  constructor I
  getType : Ty
  getUsage : Usage getType

public export
data IsPort : Item -> Type
  where
    IP : IsPort (I (TyPort (dir,type)) u)

Uninhabited (IsPort (I TyUnit u)) where
  uninhabited IP impossible

Uninhabited (IsPort (I (TyChan p) u)) where
  uninhabited IP impossible

Uninhabited (IsPort (I TyGate u)) where
  uninhabited IP impossible

export
isPort : (item : Item) -> Dec (IsPort item)
isPort (I (TyPort (d,ty)) _)
  = Yes IP

isPort (I TyUnit _)     = No absurd
isPort (I (TyChan x) _) = No absurd
isPort (I TyGate _)     = No absurd

public export
data IsChan : Item -> Type
  where
    IC : Singleton (I (TyChan type) u) -> IsChan (I (TyChan type) u)

Uninhabited (IsChan (I TyUnit u)) where
  uninhabited (IC _) impossible

Uninhabited (IsChan (I (TyPort p) u)) where
  uninhabited (IC _) impossible

Uninhabited (IsChan (I TyGate u)) where
  uninhabited (IC _) impossible

export
isChan : (item : Item) -> Dec (IsChan item)
isChan (I (TyChan x) (TyChan i o))
  = Yes (IC (Val (I (TyChan x) (TyChan i o))))

isChan (I TyUnit _)     = No absurd
isChan (I (TyPort x) _) = No absurd
isChan (I TyGate _)     = No absurd

public export
data IsGate : Item -> Type
  where
    IG : IsGate (I TyGate u)

Uninhabited (IsGate (I TyUnit u)) where
  uninhabited IC impossible

Uninhabited (IsGate (I (TyPort p) u)) where
  uninhabited IC impossible

Uninhabited (IsGate (I (TyChan ty) u)) where
  uninhabited IC impossible

export
isGate : (item : Item) -> Dec (IsGate item)
isGate (I TyUnit _)     = No absurd
isGate (I (TyPort x) _) = No absurd
isGate (I (TyChan x) _) = No absurd
isGate (I TyGate _) = Yes IG

export
DecEq Item where

  decEq (I tA uA) (I tB uB) with (decEq tA tB)
    decEq (I tA uA) (I tA uB) | (Yes Refl) with (decEq uA uB Refl)
      decEq (I tA uA) (I tA uA) | (Yes Refl) | (Yes (Same Refl Refl))
        = Yes Refl

      decEq (I tA uA) (I tA uB) | (Yes Refl) | (No no)
        = No (\Refl => no (Same Refl Refl))

    decEq (I tA uA) (I tB uB) | (No contra)
       = No (\Refl => contra Refl)


public export
data HasType : (type : Ty) -> (item : Item) -> Type where
  HT : (type : Ty) -> {u : Usage type} -> HasType type (I type u)

export
hasType : (type : Ty) -> (item : Item) -> Dec (HasType type item)
hasType type (I getType getUsage) with (decEq type getType)
  hasType type (I type getUsage) | (Yes Refl)
    = Yes (HT type)
  hasType type (I getType getUsage) | (No contra)
    = No (\(HT _) => contra Refl)

-- [ EOF ]
