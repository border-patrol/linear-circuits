||| Predicates over ports.
|||
||| Module    : Ports.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.TermType.Port

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

import Toolkit.Data.Vect.Quantifiers
import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

import Circuits.NetList.Linear.Usage.DataType
import Circuits.NetList.Linear.Usage.TermType

%default total

-- # [ Free Ports ]

-- ## [ Predicates Positive ]

public export
data IsFree : (type : Ty)
           -> (u    : Usage type)
                   -> Type
  where
    Free : (prf : IsFree               type           u)
               -> IsFree (TyPort (flow,type)) (TyPort u)

Uninhabited (IsFree (TyChan type) u) where
  uninhabited (Free prf) impossible

Uninhabited (IsFree TyGate u) where
  uninhabited (Free prf) impossible

Uninhabited (IsFree TyUnit u) where
  uninhabited (Free prf) impossible

-- ## [ Predicates Negative ]

public export
data IsFreeNot : (type : Ty)
              -> (u    : Usage type)
                      -> Type
  where
    FreeNot : (prf : IsFreeNot               type           u)
                  -> IsFreeNot (TyPort (flow,type)) (TyPort u)

    FreeNotChan : IsFreeNot (TyChan type) u
    FreeNotGate : IsFreeNot TyGate        u
    FreeNotUnit : IsFreeNot TyUnit        u

-- ## [ Decision Procedures ]

export
isFree : {type : Ty}
      -> (u    : Usage type)
              -> DecInfo (IsFreeNot type u)
                         (IsFree type u)
isFree (TyPort u) with (isFree u)
  isFree (TyPort u) | (Yes prf)
    = Yes (Free prf)

  isFree (TyPort u) | (No msg no)
    = No (FreeNot msg)
         (\(Free prf) => no prf)

isFree (TyChan ein eout)
  = No FreeNotChan
       absurd

isFree TyGate
  = No FreeNotGate
       absurd

isFree TyUnit
  = No FreeNotUnit
       absurd

-- # [ Free Ports at a specific Index ]

-- ## [ Predicates Positive ]

public export
data IsFreeAt : (idx  : List Nat)
             -> (type : Ty)
             -> (u    : Usage type)
                     -> Type
  where
    FreeAt : (prf : IsFreeAt idx               (BVECT (W (S n) ItIsSucc) type)          us)
                 -> IsFreeAt idx (TyPort (flow, BVECT (W (S n) ItIsSucc) type)) (TyPort us)

Uninhabited (IsFreeAt idx (TyChan type) u) where
  uninhabited (Free prf) impossible

Uninhabited (IsFreeAt idx TyGate u) where
  uninhabited (Free prf) impossible

Uninhabited (IsFreeAt idx TyUnit u) where
  uninhabited (Free prf) impossible


-- ## [ Predicates Negative ]

public export
data IsFreeAtNot : (idx  : List Nat)
                -> (type : Ty)
                -> (u    : Usage type)
                        -> Type
  where
    FreeAtNot : (prf : IsFreeAtNot idx               type           u)
                    -> IsFreeAtNot idx (TyPort (flow,type)) (TyPort u)

    FreeAtNotChan : IsFreeAtNot idx (TyChan type) u
    FreeAtNotGate : IsFreeAtNot idx TyGate        u
    FreeAtNotUnit : IsFreeAtNot idx TyUnit        u

-- ## [ Decision Procedure ]

export
isFreeAt : {type : Ty}
        -> (idx  : List Nat)
        -> (u    : Usage type)
                -> DecInfo (IsFreeAtNot idx type u)
                           (IsFreeAt    idx type u)
isFreeAt idx (TyPort u) with (isFreeAt idx u)
  -- [ NOTE ] Need the pattern match to ensure type is an array...
  isFreeAt [idx] (TyPort (Array us)) | (Yes (FreeAtHere prf))
    = Yes (FreeAt (FreeAtHere prf))
  isFreeAt (i :: (i'::rest)) (TyPort (Array us)) | (Yes (FreeAtThere x))
    = Yes (FreeAt (FreeAtThere x))

  isFreeAt idx (TyPort u) | (No msg no)
    = No (FreeAtNot msg)
         (\(FreeAt prf) => no prf)

isFreeAt idx (TyChan ein eout)
  = No FreeAtNotChan
       absurd

isFreeAt idx TyGate
  = No FreeAtNotGate
       absurd

isFreeAt idx TyUnit
  = No FreeAtNotUnit
       absurd

-- # [ Used Ports ]

-- ## [ Predicates Positive ]

public export
data IsUsed : (type : Ty)
           -> (u    : Usage type)
                   -> Type
  where
    Used : (prf : IsUsed               type           u)
               -> IsUsed (TyPort (flow,type)) (TyPort u)

Uninhabited (IsUsed (TyChan type) u) where
  uninhabited (Used prf) impossible

Uninhabited (IsUsed TyGate u) where
  uninhabited (Used prf) impossible

Uninhabited (IsUsed TyUnit u) where
  uninhabited (Used prf) impossible

-- ## [ Predicates Negative ]

public export
data IsUsedNot : (type : Ty)
              -> (u    : Usage type)
                      -> Type
  where
    UsedNot : (prf : IsUsedNot               type           u)
                  -> IsUsedNot (TyPort (flow,type)) (TyPort u)

    UsedNotChan : IsUsedNot (TyChan type) u
    UsedNotGate : IsUsedNot TyGate        u
    UsedNotUnit : IsUsedNot TyUnit        u

-- ## [ Decision Procedures ]

export
isUsed : {type : Ty}
      -> (u    : Usage type)
              -> DecInfo (IsUsedNot type u)
                         (IsUsed type u)
isUsed (TyPort u) with (isUsed u)
  isUsed (TyPort u) | (Yes prf)
    = Yes (Used prf)

  isUsed (TyPort u) | (No msg no)
    = No (UsedNot msg)
         (\(Used prf) => no prf)

isUsed (TyChan ein eout)
  = No UsedNotChan
       absurd

isUsed TyGate
  = No UsedNotGate
       absurd

isUsed TyUnit
  = No UsedNotUnit
       absurd

-- # [ Used Ports at a specific Index ]

-- ## [ Predicates Positive ]

public export
data IsUsedAt : (idx  : List Nat)
             -> (type : Ty)
             -> (u    : Usage type)
                     -> Type
  where
    UsedAt : (prf : IsUsedAt idx               (BVECT (W (S n) ItIsSucc) type)          us)
                 -> IsUsedAt idx (TyPort (flow, BVECT (W (S n) ItIsSucc) type)) (TyPort us)

Uninhabited (IsUsedAt idx (TyChan type) u) where
  uninhabited (Used prf) impossible

Uninhabited (IsUsedAt idx TyGate u) where
  uninhabited (Used prf) impossible

Uninhabited (IsUsedAt idx TyUnit u) where
  uninhabited (Used prf) impossible


-- ## [ Predicates Negative ]

public export
data IsUsedAtNot : (idx  : List Nat)
                -> (type : Ty)
                -> (u    : Usage type)
                        -> Type
  where
    UsedAtNot : (prf : IsUsedAtNot idx               type           u)
                    -> IsUsedAtNot idx (TyPort (flow,type)) (TyPort u)

    UsedAtNotChan : IsUsedAtNot idx (TyChan type) u
    UsedAtNotGate : IsUsedAtNot idx TyGate        u
    UsedAtNotUnit : IsUsedAtNot idx TyUnit        u

-- ## [ Decision Procedure ]

export
isUsedAt : (idx  : List Nat)
        -> {type : Ty}
        -> (u    : Usage type)
                -> DecInfo (IsUsedAtNot idx type u)
                           (IsUsedAt    idx type u)

isUsedAt idx (TyPort u) with (isUsedAt idx u)
  isUsedAt [idx] (TyPort (Array us)) | (Yes (UsedAtHere prf))
    = Yes (UsedAt (UsedAtHere prf))
  isUsedAt (i :: (i'::rest)) (TyPort (Array us)) | (Yes (UsedAtThere x))
    = Yes (UsedAt (UsedAtThere x))

  isUsedAt idx (TyPort u) | (No msg no)
    = No (UsedAtNot msg)
         (\(UsedAt prf) => no prf)

isUsedAt idx (TyChan ein eout)
  = No UsedAtNotChan
       absurd

isUsedAt idx TyGate
  = No UsedAtNotGate
       absurd

isUsedAt idx TyUnit
  = No UsedAtNotUnit
       absurd

-- [ EOF ]
