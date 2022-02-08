module Circuits.NetList.Linear.Usage.DataType

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

--import Toolkit.Data.Vect.Leanings
import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

%default total


public export
data Usage : DType -> Type where
  Logic : (u : Usage) -> Usage LOGIC

  Array : (us : Vect            (S n)           (Usage type))
             -> Usage (BVECT (W (S n) ItIsSucc)        type)

mutual
  namespace Free
    public export
    data IsFree : (type : DType) -> (u : Usage type) -> Type
      where
        FreeL : IsFree LOGIC (Logic FREE)
        FreeA : (prf : All (IsFree type) os)
                    -> IsFree (BVECT (W (S n) ItIsSucc) type) (Array os)

    Uninhabited (IsFree LOGIC (Logic USED)) where
      uninhabited FreeL impossible


  namespace Used
    public export
    data IsUsed : (type : DType) -> (u : Usage type) -> Type
      where
        UsedL : IsUsed LOGIC (Logic USED)
        UsedA : (prf : All (IsUsed type) os)
                    -> IsUsed (BVECT (W (S n) ItIsSucc) type) (Array os)

    Uninhabited (IsUsed LOGIC (Logic FREE)) where
      uninhabited UsedL impossible

  namespace Part
    public export
    data IsPart : (type : DType) -> (u : Usage type) -> Type
      where
        PartA : (notF : Any (IsFree type) os )
             -> (notU : Any (IsUsed type) os )
                     -> IsPart (BVECT (W (S n) ItIsSucc) type) (Array os)

    Uninhabited (IsPart LOGIC (Logic u)) where
      uninhabited PartA impossible

mutual

  namespace Free
    notFree : (All (IsFree type) us -> Void)
            -> IsFree (BVECT (W (S n) ItIsSucc) type) (Array us)
            -> Void
    notFree f (FreeA prf) = f prf

    export
    isFree : {type : DType}
          -> (u    : Usage type)
                  -> Dec (IsFree type u)
    isFree (Logic USED)
      = No absurd
    isFree (Logic FREE)
      = Yes FreeL

    isFree (Array us) with (all isFree us)
      isFree (Array us) | (Yes prf)
         = Yes (FreeA prf)
      isFree (Array us) | (No contra)
        = No (notFree contra)

  namespace Used
    notUsed : (All (IsUsed type) us -> Void)
           -> IsUsed (BVECT (W (S n) ItIsSucc) type) (Array us)
           -> Void
    notUsed f (UsedA prf) = f prf

    export
    isUsed : {type : DType}
          -> (u    : Usage type)
                  -> Dec (IsUsed type u)
    isUsed (Logic FREE)
      = No absurd
    isUsed (Logic USED)
      = Yes UsedL

    isUsed (Array us) with (all isUsed us)
      isUsed (Array us) | (Yes prf)
         = Yes (UsedA prf)
      isUsed (Array us) | (No contra)
        = No (notUsed contra)

  namespace Part

    export
    isPart : {type : DType}
          -> (u    : Usage type)
                  -> Dec (IsPart type u)
    isPart (Logic u)
      = No absurd

    isPart (Array us) with (any isFree us)
      isPart (Array us) | (Yes prfF) with (any isUsed us)
        isPart (Array us) | (Yes prfF) | (Yes prfU)
          = Yes (PartA prfF prfU)
        isPart (Array us) | (Yes prfF) | (No contra)
          = No (\(PartA fs us) => contra us)

      isPart (Array us) | (No contra)
        = No (\(PartA fs us) => contra fs)


public export
data IsFreeAt : (idx : Fin n) -> (type : DType) -> (u : Usage type) -> Type
  where
    FreeAt : {idx : Fin m}
          -> {us  : Vect (S n) (Usage type)}
          -> (prf : AtIndexI (Usage type) (IsFree type) m (S n) idx us)
                 -> IsFreeAt idx (BVECT (W (S n) ItIsSucc) type) (Array us)

Uninhabited (IsFreeAt idx LOGIC u) where
  uninhabited (FreeAt prf) impossible


notFreeAtIndex : (AtIndexI (Usage type) (IsFree type) m (S n) idx us -> Void)
              -> IsFreeAt idx (BVECT (W (S n) ItIsSucc) type) (Array us) -> Void
notFreeAtIndex f (FreeAt prf) = f  prf

export
isFreeAt : {type : DType}
        -> {n   : Nat}
        -> (idx : Fin n)
        -> (u   : Usage type)
               -> Dec (IsFreeAt idx type u)

isFreeAt {n = n} idx (Logic u)
  = No absurd

isFreeAt {n = n} idx (Array us) with (atIndexI isFree idx us)
  isFreeAt {n = (S n)} idx (Array us) | (Yes prf)
    = Yes (FreeAt prf)

  isFreeAt {n = n} idx (Array us) | (No contra)
    = No (notFreeAtIndex contra)


public export
data IsUsedAt : (idx : Fin n) -> (type : DType) -> (u : Usage type) -> Type
  where
    UsedAt : {idx : Fin m}
          -> (prf : AtIndexI (Usage type) (IsUsed type) m (S n) idx us)
                 -> IsUsedAt idx (BVECT (W (S n) ItIsSucc) type) (Array us)

Uninhabited (IsUsedAt idx LOGIC u) where
  uninhabited (UsedAt prf) impossible

notUsedAtIndex : (AtIndexI (Usage type) (IsUsed type) m (S n) idx us -> Void)
               -> IsUsedAt idx (BVECT (W (S n) ItIsSucc) type) (Array us) -> Void
notUsedAtIndex f (UsedAt prf) = f prf


export
isUsedAt : {type : DType}
        -> {n   : Nat}
        -> (idx : Fin n)
        -> (u   : Usage type)
               -> Dec (IsUsedAt idx type u)

isUsedAt {n = n} idx (Logic u)
  = No absurd

isUsedAt {n = n} idx (Array us) with (atIndexI isUsed idx us)
  isUsedAt {n = (S n)} idx (Array us) | (Yes prf)
    = Yes (UsedAt prf)

  isUsedAt {n = n} idx (Array us) | (No contra)
    = No (notUsedAtIndex contra)


mutual

  export
  init : (type : DType) -> DPair (Usage type) (IsFree type)
  init LOGIC
    = MkDPair (Logic FREE) FreeL

  init (BVECT (W (S n) ItIsSucc) type) with (init type)
    init (BVECT (W (S n) ItIsSucc) type) | (MkDPair u prf) with (init (S n) u prf)
      init (BVECT (W (S n) ItIsSucc) type) | (MkDPair u prf) | (MkDPair os pU)
        = MkDPair (Array os) (FreeA pU)

  namespace Vect
    export
    init : (n   : Nat)
        -> (u   : Usage type)
        -> (prf : IsFree type u)
               -> DPair (Vect n (Usage type)) (All (IsFree type))
    init Z _ _ = MkDPair [] []
    init (S k) u prf with (init k u prf)
      init (S k) u prf | (MkDPair fst snd)
        = MkDPair (u :: fst) (prf :: snd)

-- [ EOF ]
