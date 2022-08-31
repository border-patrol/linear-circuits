||| Predicates to denote full used.
|||
||| Module    : DataType.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.DataType.Used

import        Decidable.Equality

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed

import        Data.Vect
import public Data.Vect.Quantifiers

import        Toolkit.Data.Whole

import public Toolkit.Data.Vect.Quantifiers

import        Circuits.Common
import        Circuits.NetList.Types

import        Circuits.NetList.Linear.Usage.DataType.Def

%default total

||| The datatype has not been used.
public export
data IsUsed : (type : DType)
           -> (u    : Usage type)
                   -> Type
  where
    UsedL : IsUsed LOGIC
                   (Logic USED)

    UsedA : (prf : All (IsUsed type) os)
                -> IsUsed (BVECT (W (S n) ItIsSucc) type)
                          (Array os)
export
Uninhabited (IsUsed LOGIC (Logic FREE)) where
  uninhabited UsedL impossible


||| A datatype to capture non-free usages.
public export
data IsUsedNot : (type : DType)
              -> (u    : Usage type)
                      -> Type
  where
    NotUsedL : IsUsedNot LOGIC (Logic FREE)
    NotUsedA : NotAll (IsUsed    type)
                      (IsUsedNot type)
                      us
            -> IsUsedNot (BVECT (W (S n) ItIsSucc) type)
                         (Array us)

export
isUsed : (u : Usage type)
           -> DecInfo (IsUsedNot type u)
                      (IsUsed    type u)
isUsed (Logic FREE)
  = No NotUsedL
       absurd

isUsed (Logic USED)
  = Yes UsedL

isUsed (Array us) with (Informative.all isUsed us)
  isUsed (Array us) | (Yes prf)
    = Yes (UsedA prf)
  isUsed (Array us) | (No neg no)
    = No (NotUsedA neg)
         (\(UsedA prf) => no prf)


-- [ EOF ]
