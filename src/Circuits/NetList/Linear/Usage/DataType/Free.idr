||| Predicates to denote full freedom
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.DataType.Free

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
data IsFree : (type : DType)
           -> (u    : Usage type)
                   -> Type
  where
    FreeL : IsFree LOGIC
                   (Logic FREE)

    FreeA : (prf : All (IsFree type) os)
                -> IsFree (BVECT (W (S n) ItIsSucc) type)
                          (Array os)
export
Uninhabited (IsFree LOGIC (Logic USED)) where
  uninhabited FreeL impossible


||| A datatype to capture non-free usages.
public export
data IsFreeNot : (type : DType)
              -> (u    : Usage type)
                      -> Type
  where
    NotFreeL : IsFreeNot LOGIC (Logic USED)
    NotFreeA : NotAll (IsFree    type)
                      (IsFreeNot type)
                      us
            -> IsFreeNot (BVECT (W (S n) ItIsSucc) type)
                         (Array us)

export
isFree : (u : Usage type)
           -> DecInfo (IsFreeNot type u)
                      (IsFree    type u)
isFree (Logic USED)
  = No NotFreeL
       absurd

isFree (Logic FREE)
  = Yes FreeL

isFree (Array us) with (Informative.all isFree us)
  isFree (Array us) | (Yes prf)
    = Yes (FreeA prf)
  isFree (Array us) | (No neg no)
    = No (NotFreeA neg)
         (\(FreeA prf) => no prf)


-- [ EOF ]
