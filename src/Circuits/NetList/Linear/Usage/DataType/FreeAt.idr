||| Predicates to denote full freedom
|||
||| Module    : DataType.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.DataType.FreeAt

import        Decidable.Equality

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed

import        Data.Vect
import        Data.Vect.Quantifiers
import public Data.Vect.AtIndex

import        Toolkit.Data.Fin
import public Toolkit.Data.DVect

import public Toolkit.Data.Vect.Extra

import public Toolkit.Data.Vect.Quantifiers

import        Circuits.Common
import        Circuits.NetList.Types

import public Circuits.NetList.Linear.Usage.DataType.Def
import        Circuits.NetList.Linear.Usage.DataType.Free

%default total

mutual
  ||| Proof that at the end of the set of indicies the usage is set to
  ||| free.
  public export
  data IsFreeAt : (idx  : List Nat)
               -> (type : DType)
               -> (u    : Usage type)
                       -> Type
   where

     ||| At the inner most index, so try and see if the element is free.
     FreeAtHere : {idx : Nat}
               -> {us  : Vect (S n) (Usage type)}
               -> (prf : AtIndex (Usage type)
                                 (IsFree    type)
                                 (IsFreeNot type)
                                 idx
                                 us)
                     -> IsFreeAt (idx::Nil)
                                 (BVECT (W (S n) ItIsSucc)
                                        type)
                                 (Array us)

     ||| Stepping down the dimensions.
     FreeAtThere : {idx  : Nat}
                -> {us   : Vect (S n) (Usage type)}
                -> (rest : AtIndex (Usage type)
                                   (IsFreeAt    (idx'::idxs) type)
                                   (IsFreeAtNot (idx'::idxs) type)
                                   idx
                                   us)
                -> IsFreeAt (idx::(idx'::idxs))
                            (BVECT (W (S n) ItIsSucc)
                                   type)
                            (Array us)

  ||| Some 'informative' error messages...
  public export
  data IsFreeAtNot : (idx  : List Nat)
                  -> (type : DType)
                  -> (u    : Usage type)
                          -> Type
    where
      FreeAtNotL : IsFreeAtNot idx LOGIC u
      FreeAtBadIdx : IsFreeAtNot idx type u
      FreeAtNotEmpty : IsFreeAtNot Nil type u

      FreeAtNotHere : IsFreeAtNot [idx]
                                  (BVECT (W (S n) ItIsSucc) type)
                                  (Array us)

      FreeAtNotThere : AtIndexNot (Usage type)
                                  (IsFreeAt (i'::is) type)
                                  (IsFreeAtNot (i'::is) type)
                                  i
                                  us
                    -> IsFreeAtNot (i::(i'::is))
                                   (BVECT (W (S n) ItIsSucc) type)
                                   (Array us)

-- [ NOTE ] Uninhabited instances

Uninhabited (IsFreeAt idx LOGIC u) where
  uninhabited (FreeAtHere prf) impossible
  uninhabited (FreeAtThere rest) impossible

Uninhabited (IsFreeAt Nil (BVECT w type) u) where
  uninhabited (FreeAtHere prf) impossible
  uninhabited (FreeAtThere rest) impossible




||| Decision procedure that, when given a 'path' of indices, works out
||| if the end of the path is free.
export
isFreeAt : {type : _}
        -> (idx  : List Nat)
        -> (u    : Usage type)
                -> DecInfo (IsFreeAtNot idx type u)
                           (IsFreeAt    idx type u)
isFreeAt [] (Logic u)
  = No FreeAtNotL
       absurd
isFreeAt (x :: xs) (Logic u)
  = No FreeAtNotL
       absurd

isFreeAt [] (Array us)
  = No FreeAtNotEmpty
       absurd

isFreeAt (x :: xs) (Array us) with (xs)
  isFreeAt (x :: xs) (Array us) | [] with (atIndex isFree x us)
    isFreeAt (x :: xs) (Array us) | [] | (Yes prf)
      = Yes (FreeAtHere prf)

    isFreeAt (x :: xs) (Array us) | [] | (No msg no)
      = No FreeAtNotHere
           (\(FreeAtHere prf) => no prf)

  isFreeAt (x :: xs) (Array us) | (y :: ys) with (atIndex (isFreeAt (y::ys)) x us)
    isFreeAt (x :: xs) (Array us) | (y :: ys) | (Yes prf)
      = Yes (FreeAtThere prf)
    isFreeAt (x :: xs) (Array us) | (y :: ys) | (No msg no)
      = No  (FreeAtNotThere msg)
            (\(FreeAtThere prf) => no prf)

-- [ EOF ]
