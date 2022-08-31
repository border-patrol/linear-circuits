||| Use partially used data structures.
|||
||| Module    : Partial.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.DataType.Use.Partial

import Decidable.Equality

import Data.Nat
import Data.Fin
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.DVect
import Toolkit.Data.Vect.Extra
import Toolkit.Data.Vect.Quantifiers

import Circuits.Common
import Circuits.NetList.Types
import Circuits.NetList.Linear.Usage.DataType

import Circuits.NetList.Linear.Usage.DataType.Use.Full

%default total

-- # [ Definitions ]

mutual

-- ## [ Use Some of the Things ]

  public export
  data UseAt : (is   : List Nat)

            -> (type : DType)
            -> (old  : Usage       type)
            -> (prfF : IsFreeAt is type old)
            -> (new  : Usage       type)
            -> (prfU : IsUsedAt is type new)
                    -> Type
    where
      UH : UseAt  idx                            type        fs              prfFS         us              prfUS
        -> UseAt [idx] (BVECT (W (S a) ItIsSucc) type) (Array fs) (FreeAtHere prfFS) (Array us) (UsedAtHere prfUS)

      UL : UseAt  i  (i'::is)                            type         fs               pL         us               pU
       ->  UseAt (i::(i'::is)) (BVECT (W (S a) ItIsSucc) type) (Array fs) (FreeAtThere pL) (Array us) (UsedAtThere pU)


  namespace AtIndex
    public export
    data UseAt : (i : Nat)
              -> (is : List Nat)
              -> (type : DType)
              -> (old  : Vect n   (Usage type))
              -> (this : AtIndex  (Usage type) (IsFreeAt is type) (IsFreeAtNot is type) i old)
              -> (new  : Vect n   (Usage type))
              -> (that : AtIndex  (Usage type) (IsUsedAt is type) (IsUsedAtNot is type) i new)
                      -> Type
      where
        Here : Partial.UseAt    rest type  f            pF    u           pU
            -> UseAt Z          rest type (f::fs) (Here pF) (u::fs) (Here pU)

        There : UseAt    next  rest type         fs         flater          us         ulater
             -> UseAt (S next) rest type (not_f::fs) (There flater) (not_f::us) (There ulater)

  namespace Vect
    public export
    data UseAt : (idx  : Nat)
              -> (type : DType)
              -> (old  : Vect n   (Usage type))
              -> (this : AtIndex (Usage type) (IsFree type) (IsFreeNot type) idx old)
              -> (new  : Vect n  (Usage type))
              -> (that : AtIndex (Usage type) (IsUsed type) (IsUsedNot type) idx new)
                      -> Type
      where
        Here : (use : Use     type  f            prfF   u            prfU)
                   -> UseAt Z type (f::fs) (Here prfF) (u::fs) (Here prfU)

        Next : UseAt    next  type         fs         next_f          us         next_u
            -> UseAt (S next) type (not_f::fs) (There next_f) (not_f::us) (There next_u)


-- ## [ Return Results ]
mutual


  public export
  data Result : (is   : List Nat)
             -> (type : DType)
             -> (old  : Usage       type)
             -> (free : IsFreeAt is type  old)
                     -> Type
    where
      R : {prfF  : IsFreeAt is type old}
       -> (new   : Usage       type)
       -> (prfU  : IsUsedAt is type          new)
       -> (holds : UseAt    is type old prfF new prfU)
                -> Result   is type old prfF

  namespace AtIndex
    public export
    data Result : (i    : Nat)
               -> (is   : List Nat)
               -> (type : DType)
               -> (old  : Vect n  (Usage type))
               -> (this : AtIndex (Usage type) (IsFreeAt is type) (IsFreeAtNot is type) i old)
                       -> Type
      where
        R : {this  : AtIndex (Usage type) (IsFreeAt is type) (IsFreeAtNot is type) i old}
         -> (new   : Vect n  (Usage type))
         -> (prfU  : AtIndex (Usage type) (IsUsedAt is type) (IsUsedAtNot is type) i new)
         -> (holds : UseAt  i is        type old this new prfU)
                  -> Result i is        type old this

  namespace Vect
    public export
    data Result : (idx  : Nat)
               -> (type : DType)
               -> (old  : Vect n (Usage type))
               -> (this : AtIndex (Usage type) (IsFree type) (IsFreeNot type) idx old)
                       -> Type
      where
        R : (new   : Vect n   (Usage type))
         -> (prfU  : AtIndex (Usage type) (IsUsed type) (IsUsedNot type) idx new)
         -> (holds : UseAt  idx type old this new prfU)
                  -> Result idx type old this


-- # [ Actually Use All the Things ]

mutual

  export
  useAt : (idx  : List Nat)
       -> {old  : Usage        type}
       -> (free : IsFreeAt idx type old)
               -> Result   idx type old free
  useAt [idx] (FreeAtHere prf) with (useAt idx prf)
    useAt [idx] (FreeAtHere prf) | (R new prfU holds)
      = R (Array new) (UsedAtHere prfU) (UH holds)
  useAt (idx :: (idx' :: idxs)) (FreeAtThere rest) with (useAt idx (idx'::idxs) rest)
    useAt (idx :: (idx' :: idxs)) (FreeAtThere rest) | (R new prfU holds)
      = R (Array new) (UsedAtThere prfU) (UL holds)

  namespace AtIndex
    export
    useAt : (i    : Nat)
         -> (is   : List Nat)
         -> {old  : Vect n   (Usage type)}
         -> (this : AtIndex  (Usage type) (IsFreeAt    is type)
                                          (IsFreeAtNot is type) i old)
                 -> Result i is type old this
    useAt Z is (Here prf) with (useAt is prf)
      useAt Z is (Here prf) | (R new prfU holds)
        = R (new :: _) (Here prfU) (Here holds)

    useAt (S k) is (There later) with (useAt k is later)
      useAt (S k) is (There later) | (R new prfU holds)
        = R (_ :: new) (There prfU) (There holds)

  namespace Vect

    export
    useAt : (idx  : Nat)
         -> {old  : Vect n (Usage type)}
         -> (this : AtIndex (Usage type) (IsFree type) (IsFreeNot type) idx old)
                 -> Result idx type old this
    useAt Z (Here prf) with (use prf)
      useAt Z (Here prf) | (R u used result)
       = R _ (Here used) (Here result)
    useAt (S k) (There later) with (useAt k later)
      useAt (S k) (There later) | (R new prfU holds)
        = R _ (There prfU) (Next holds)

-- [ EOF ]
