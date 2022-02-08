module Circuits.NetList.Linear.Usage.DataType.Use.Partial

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

import Circuits.Common
import Circuits.NetList.Types
import Circuits.NetList.Linear.Usage.DataType

import Circuits.NetList.Linear.Usage.DataType.Use.Full

%default total

mutual
  public export
  data Use : (idx  : Fin m)

          -> (type : DType)
          -> (old  : Usage        (BVECT (W (S n) ItIsSucc) type))
          -> (prfF : IsFreeAt idx (BVECT (W (S n) ItIsSucc) type)  old)

          -> (new  : Usage        (BVECT (W (S n) ItIsSucc) type))
          -> (prfU : IsUsedAt idx (BVECT (W (S n) ItIsSucc) type)  new)
                  -> Type
    where
      UA : Use idx type        fs          prfFS         us          prfUS
        -> Use idx type (Array fs) (FreeAt prfFS) (Array us) (UsedAt prfUS)

  public export
  data Result : (idx  : Fin m)
             -> (type : DType)
             -> (old  : Usage        (BVECT (W (S n) ItIsSucc) type))
             -> (free : IsFreeAt idx (BVECT (W (S n) ItIsSucc) type)  old)
                     -> Type
    where
      R : (new   : Usage        (BVECT (W (S n) ItIsSucc) type))
       -> (prfU  : IsUsedAt idx (BVECT (W (S n) ItIsSucc) type)         new)
       -> (holds : Use      idx                           type old prfF new prfU)
                -> Result   idx                           type old prfF

  namespace Vect
    public export
    data Use : (idx  : Fin  m)
            -> (type : DType)
            -> (old  : Vect n   (Usage type))
            -> (this : AtIndexI (Usage type) (IsFree type) m n idx old)
            -> (new  : Vect n   (Usage type))
            -> (that : AtIndexI (Usage type) (IsUsed type) m n idx new)
                    -> Type
      where
        Here : (use : Use    type  f                prfF    u                prfU)
                   -> Use FZ type (f::fs) (At (Here prfF)) (u::fs) (At (Here prfU))

        Next : Use     next  type         fs  (At        next_f)          us  (At        next_u)
            -> Use (FS next) type (not_f::fs) (At (There next_f)) (not_u::us) (At (There next_u))

    public export
    data Result : (idx  : Fin m)
               -> (type : DType)
               -> (old  : Vect n (Usage type))
               -> (this : AtIndexI (Usage type) (IsFree type) m n idx old)
                       -> Type
      where
        R : (new   : Vect n   (Usage type))
         -> (prfU  : AtIndexI (Usage type) (IsUsed type) m n idx new)
         -> (holds : Use    idx type old this new prfU)
                  -> Result idx type old this


mutual


  use : {type : DType}
     -> (idx  : Fin m)
     -> {old  : Usage        (BVECT (W (S n) ItIsSucc) type)}
     -> (free : IsFreeAt idx (BVECT (W (S n) ItIsSucc) type) old)
             -> Result   idx                           type old free
  use idx (FreeAt prf) with (use idx prf)
    use idx (FreeAt prf) | (R new prfU holds)
      = R (Array new) (UsedAt prfU) (UA holds)


  namespace Vect

    export
    use : {type : DType}
       -> (idx  : Fin m)
       -> {old  : Vect n (Usage type)}
       -> (this : AtIndexI (Usage type) (IsFree type) m n idx old)
               -> Result idx type old this
    use FZ {old=(x :: xs)} (At (Here prf)) with (use prf)
      use FZ {old=(x :: xs)} (At (Here prf)) | (R u used result)
        = R (u :: xs) (At (Here used)) (Here result)

    use (FS next) {old=(not_x :: xs)} (At (There later)) with (use next (At later))
      use (FS next) {old=(not_x :: xs)} (At (There later)) | (R new (At x) holds)
        = R (not_x :: new) (At (There x)) (Next holds)

-- [ EOF ]
