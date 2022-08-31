||| Predicates to denote full used.
|||
||| Module    : UsedAt.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.DataType.UsedAt

import        Decidable.Equality

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed

import        Data.Vect
import        Data.Vect.Quantifiers
import public Data.Vect.AtIndex

import        Toolkit.Data.Whole
import public Toolkit.Data.DVect

import public Toolkit.Data.Vect.Extra

import public Toolkit.Data.Vect.Quantifiers

import        Circuits.Common
import        Circuits.NetList.Types

import public Circuits.NetList.Linear.Usage.DataType.Def
import        Circuits.NetList.Linear.Usage.DataType.Used

%default total

mutual
  ||| Proof that at the end of the set of indicies the usage is set to
  ||| free.
  public export
  data IsUsedAt : (idx  : List Nat)
               -> (type : DType)
               -> (u    : Usage type)
                       -> Type
   where

     ||| At the inner most index, so try and see if the element is free.
     UsedAtHere : {idx : Nat}
               -> {us  : Vect (S n) (Usage type)}
               -> (prf : AtIndex (Usage type)
                                 (IsUsed    type)
                                 (IsUsedNot type)
                                 idx
                                 us)
                     -> IsUsedAt (idx::Nil)
                                 (BVECT (W (S n) ItIsSucc)
                                        type)
                                 (Array us)

     ||| Stepping down the dimensions.
     UsedAtThere : {idx  : Nat}
                -> {us   : Vect (S n) (Usage type)}
                -> (rest : AtIndex (Usage type)
                                   (IsUsedAt    (idx'::idxs) type)
                                   (IsUsedAtNot (idx'::idxs) type)
                                   idx
                                   us)
                -> IsUsedAt (idx::(idx'::idxs))
                            (BVECT (W (S n) ItIsSucc)
                                   type)
                            (Array us)

  ||| Some 'informative' error messages...
  public export
  data IsUsedAtNot : (idx  : List Nat)
                  -> (type : DType)
                  -> (u    : Usage type)
                          -> Type
    where
      UsedAtNotL : IsUsedAtNot idx LOGIC u
      UsedAtBadIdx : IsUsedAtNot idx type u
      UsedAtNotEmpty : IsUsedAtNot Nil type u

      UsedAtNotHere : IsUsedAtNot [idx]
                                  (BVECT (W (S n) ItIsSucc) type)
                                  (Array us)

      UsedAtNotThere : AtIndexNot (Usage type)
                                  (IsUsedAt (i'::is) type)
                                  (IsUsedAtNot (i'::is) type)
                                  i
                                  us
                    -> IsUsedAtNot (i::(i'::is))
                                   (BVECT (W (S n) ItIsSucc) type)
                                   (Array us)

-- [ NOTE ] Uninhabited instances

Uninhabited (IsUsedAt idx LOGIC u) where
  uninhabited (UsedAtHere prf) impossible
  uninhabited (UsedAtThere rest) impossible

Uninhabited (IsUsedAt Nil (BVECT w type) u) where
  uninhabited (UsedAtHere prf) impossible
  uninhabited (UsedAtThere rest) impossible




||| Decision procedure that, when given a 'path' of indices, works out
||| if the end of the path is free.
export
isUsedAt : {type : _}
        -> (idx  : List Nat)
        -> (u    : Usage type)
                -> DecInfo (IsUsedAtNot idx type u)
                           (IsUsedAt    idx type u)
isUsedAt [] (Logic u)
  = No UsedAtNotL
       absurd
isUsedAt (x :: xs) (Logic u)
  = No UsedAtNotL
       absurd

isUsedAt [] (Array us)
  = No UsedAtNotEmpty
       absurd

isUsedAt (x :: xs) (Array us) with (xs)
  isUsedAt (x :: xs) (Array us) | [] with (atIndex isUsed x us)
    isUsedAt (x :: xs) (Array us) | [] | (Yes prf)
      = Yes (UsedAtHere prf)

    isUsedAt (x :: xs) (Array us) | [] | (No msg no)
      = No UsedAtNotHere
           (\(UsedAtHere prf) => no prf)

  isUsedAt (x :: xs) (Array us) | (y :: ys) with (atIndex (isUsedAt (y::ys)) x us)
    isUsedAt (x :: xs) (Array us) | (y :: ys) | (Yes prf)
      = Yes (UsedAtThere prf)
    isUsedAt (x :: xs) (Array us) | (y :: ys) | (No msg no)
      = No  (UsedAtNotThere msg)
            (\(UsedAtThere prf) => no prf)

-- [ EOF ]
