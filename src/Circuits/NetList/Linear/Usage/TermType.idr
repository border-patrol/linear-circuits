module Circuits.NetList.Linear.Usage.TermType

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

import Circuits.NetList.Linear.Usage.DataType
import Circuits.NetList.Linear.Usage.DataType.Use.Full
import Circuits.NetList.Linear.Usage.DataType.Use.Partial

%default total


public export
data Usage : Ty -> Type where
  TyPort : (u : Usage                type)
             -> Usage (TyPort (flow, type))

  TyChan : (ein  : Usage         type)
        -> (eout : Usage         type)
                -> Usage (TyChan type)

  TyGate : Usage TyGate
  TyUnit : Usage TyUnit


namespace Free

  public export
  data IsFree : (type : Ty) -> (u : Usage type) -> Type
    where
      FreeP : (prf : IsFree type u)
                  -> IsFree (TyPort (flow,type)) (TyPort u)

      FreeCB : (pin  : IsFree type a)
            -> (pout : IsFree type b)
                    -> IsFree (TyChan type) (TyChan a b)

      FreeG : IsFree TyGate TyGate
      FreeU : IsFree TyUnit TyUnit

  export
  isFree : {type : Ty} -> (u : Usage type) -> Dec (IsFree type u)
  isFree (TyPort x) with (isFree x)
    isFree (TyPort x) | (Yes prf)
      = Yes (FreeP prf)
    isFree (TyPort x) | (No contra)
      = No (\(FreeP prf) => contra prf)

  isFree (TyChan x y) with (isFree x)
    isFree (TyChan x y) | (Yes prfX) with (isFree y)
      isFree (TyChan x y) | (Yes prfX) | (Yes prfY)
        = Yes (FreeCB prfX prfY)
      isFree (TyChan x y) | (Yes prfX) | (No contra)
        = No (\(FreeCB a b) => contra b)
    isFree (TyChan x y) | (No contra)
      = No (\(FreeCB a b) => contra a)

  isFree TyGate
    = Yes FreeG

  isFree TyUnit
    = Yes FreeU

namespace Used

  public export
  data IsUsed : (type : Ty) -> (u : Usage type) -> Type where
    UsedP : IsUsed type u -> IsUsed (TyPort (flow,type)) (TyPort u)

    UsedC : (uin : IsUsed ty a)
         -> (uou : IsUsed ty b )
                -> IsUsed (TyChan ty) (TyChan a b)

  Uninhabited (IsUsed TyGate u) where
    uninhabited (UsedP x) impossible

  Uninhabited (IsUsed TyUnit u) where
    uninhabited (UsedP x) impossible

  export
  isUsed : {type : Ty} -> (u : Usage type) -> Dec (IsUsed type u)
  isUsed (TyPort x) with (isUsed x)
    isUsed (TyPort x) | (Yes prf)
      = Yes (UsedP prf)
    isUsed (TyPort x) | (No contra)
      = No (\(UsedP prf) => contra prf)

  isUsed (TyChan x y) with (isUsed x)
    isUsed (TyChan x y) | (Yes prfX) with (isUsed y)
      isUsed (TyChan x y) | (Yes prfX) | (Yes prfY)
        = Yes (UsedC prfX prfY)
      isUsed (TyChan x y) | (Yes prfX) | (No contra)
        = No (\(UsedC a b) => contra b)
    isUsed (TyChan x y) | (No contra)
      = No (\(UsedC a b) => contra a)

  isUsed TyGate = No absurd
  isUsed TyUnit = No absurd

namespace Part

  public export
  data IsPart : (type : Ty) -> (u : Usage type) -> Type where
    PartP : IsPart type u
         -> IsPart (TyPort (flow,type)) (TyPort u)

    PartCI : (uin : IsPart ty a)
                 -> IsPart (TyChan ty) (TyChan a b)

    PartCO : (uin : IsPart ty b)
                 -> IsPart (TyChan ty) (TyChan a b)

  Uninhabited (IsPart TyGate u) where
    uninhabited (PartP x) impossible

  Uninhabited (IsPart TyUnit u) where
    uninhabited (PartP x) impossible

  portNotPart : (IsPart type u -> Void) -> IsPart (TyPort (flow, type)) (TyPort u) -> Void
  portNotPart f (PartP x) = f x

  chanNotPart : (IsPart type eout -> Void) -> (IsPart type ein -> Void) -> IsPart (TyChan type) (TyChan ein eout) -> Void
  chanNotPart f g (PartCI uin) = g uin
  chanNotPart f g (PartCO uin) = f uin

  export
  isPart : {type : Ty} -> (u : Usage type) -> Dec (IsPart type u)
  isPart (TyPort u) with (isPart u)
    isPart (TyPort u) | (Yes prf)
      = Yes (PartP prf)

    isPart (TyPort u) | (No contra)
      = No (portNotPart contra)

  isPart (TyChan ein eout) with (isPart ein)
    isPart (TyChan ein eout) | (Yes prf)
      = Yes (PartCI prf)

    isPart (TyChan ein eout) | (No cin) with (isPart eout)
      isPart (TyChan ein eout) | (No cin) | (Yes prf)
        = Yes (PartCO prf)

      isPart (TyChan ein eout) | (No cin) | (No cou)
        = No (chanNotPart cou cin)

  isPart TyGate = No absurd
  isPart TyUnit = No absurd



public export
data IsFreeAt : (idx : Fin n) -> (type : Ty) -> (u : Usage type) -> Type
  where
    FreeAt : (prf : IsFreeAt idx              (BVECT (W (S n) ItIsSucc) type)          us)
                 -> IsFreeAt idx (TyPort (flow,BVECT (W (S n) ItIsSucc) type)) (TyPort us)

Uninhabited (IsFreeAt idx TyGate u) where
  uninhabited (FreeAt prf) impossible

Uninhabited (IsFreeAt idx TyUnit u) where
  uninhabited (FreeAt prf) impossible

Uninhabited (IsFreeAt idx (TyChan type) u) where
  uninhabited (FreeAt prf) impossible


isNotFreeAt : (IsFreeAt idx type u -> Void) -> IsFreeAt idx (TyPort (flow, type)) (TyPort u) -> Void
isNotFreeAt f (FreeAt prf) = f prf

export
isFreeAt : {n    : Nat}
        -> {type : Ty}
        -> (idx  : Fin n)
        -> (u    : Usage type)
                -> Dec (IsFreeAt idx type u)

isFreeAt idx (TyPort u) with (isFreeAt idx u)
  isFreeAt idx (TyPort (Array us)) | (Yes (FreeAt prf))
    = Yes (FreeAt (FreeAt prf))

  isFreeAt idx (TyPort u) | (No contra)
    = No (isNotFreeAt contra)

isFreeAt idx (TyChan ein eout) = No absurd
isFreeAt idx TyGate = No absurd
isFreeAt idx TyUnit = No absurd

public export
data IsUsedAt : (idx : Fin n) -> (type : Ty) -> (u : Usage type) -> Type
  where
    UsedAt : (prf : IsUsedAt idx              (BVECT (W (S n) ItIsSucc) type)          us)
                 -> IsUsedAt idx (TyPort (flow,BVECT (W (S n) ItIsSucc) type)) (TyPort us)


Uninhabited (IsUsedAt idx TyGate u) where
  uninhabited (UsedAt prf) impossible

Uninhabited (IsUsedAt idx TyUnit u) where
  uninhabited (UsedAt prf) impossible

Uninhabited (IsUsedAt idx (TyChan type) u) where
  uninhabited (UsedAt prf) impossible

isNotUsedAt : (IsUsedAt idx type u -> Void) -> IsUsedAt idx (TyPort (flow, type)) (TyPort u) -> Void
isNotUsedAt f (UsedAt prf) = f prf

export
isUsedAt : {n    : Nat}
        -> {type : Ty}
        -> (idx  : Fin n)
        -> (u    : Usage type)
                -> Dec (IsUsedAt idx type u)

isUsedAt idx (TyPort u) with (isUsedAt idx u)
  isUsedAt idx (TyPort (Array us)) | (Yes (UsedAt prf))
    = Yes (UsedAt (UsedAt prf))

  isUsedAt idx (TyPort u) | (No contra)
    = No (isNotUsedAt contra)

isUsedAt idx (TyChan ein eout) = No absurd
isUsedAt idx TyGate = No absurd
isUsedAt idx TyUnit = No absurd

-- [ EOF ]
