module Circuits.NetList.Linear.Usage.TermType.Use.Channel

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

import Circuits.NetList.Linear.Usage.TermType

%default total


public export
data CanProject : (how  : Project dir)
               -> (type : Ty)
               -> (u    : Usage type)
                       -> Type
  where
    ProjectWrite : (prf : IsFree                   type          ein)
                       -> CanProject WRITE (TyChan type) (TyChan ein eout)

    ProjectRead : (prf : IsFree                  type              eout)
                      -> CanProject READ (TyChan type) (TyChan ein eout)

Uninhabited (CanProject how TyGate u) where
  uninhabited (ProjectWrite prf) impossible
  uninhabited (ProjectRead prf) impossible

Uninhabited (CanProject how TyUnit u) where
  uninhabited (ProjectWrite prf) impossible
  uninhabited (ProjectRead prf) impossible

Uninhabited (CanProject how (TyPort (f,dtype)) u) where
  uninhabited (ProjectWrite prf) impossible
  uninhabited (ProjectRead prf) impossible

cannotWriteTo : (IsFree type ein -> Void) -> CanProject WRITE (TyChan type) (TyChan ein eout) -> Void
cannotWriteTo f (ProjectWrite prf) = f prf

cannotReadFrom : (IsFree type eout -> Void) -> CanProject READ (TyChan type) (TyChan ein eout) -> Void
cannotReadFrom f (ProjectRead prf) = f prf

export
canProject : {type : Ty}
          -> (how : Project dir)
          -> (u   : Usage type)
                 -> Dec (CanProject how type u)
canProject how (TyPort u) = No absurd

canProject WRITE (TyChan ein eout) with (isFree ein)
  canProject WRITE (TyChan ein eout) | (Yes prf)
    = Yes (ProjectWrite prf)

  canProject WRITE (TyChan ein eout) | (No contra)
    = No (cannotWriteTo contra)

canProject READ (TyChan ein eout) with (isFree eout)
  canProject READ (TyChan ein eout) | (Yes prf)
    = Yes (ProjectRead prf)

  canProject READ (TyChan ein eout) | (No contra)
    = No (cannotReadFrom contra)

canProject how TyGate = No absurd
canProject how TyUnit = No absurd


public export
data Use : (how  : Project dir)
        -> (type : Ty)
        -> (old  : Usage type)
        -> (prf  : CanProject how type old)
        -> (new  : Usage type)
                -> Type

  where
    IsWrite : Use               type          ein                     free          newU       prf
           -> Use WRITE (TyChan type) (TyChan ein eout) (ProjectWrite free) (TyChan newU eout)

    IsRead : Use              type             eout               free              newU  prf
          -> Use READ (TyChan type)(TyChan ein eout) (ProjectRead free) (TyChan ein newU)


public export
data Result : (how  : Project dir)
           -> (type : Ty)
           -> (old  : Usage type)
           -> (prf  : CanProject how type old)
                   -> Type
  where
    R : (new : Usage  (TyChan type))
     -> (prf : Use    how (TyChan type) old proj new)
            -> Result how (TyChan type) old proj

export
use : {type : Ty}
   -> {how  : Project dir}
   -> {old  : Usage type}
   -> (prf  : CanProject how type old)
           -> Result     how type old prf
use (ProjectWrite prf) with (use prf)
  use (ProjectWrite prf) | (R u used result)
    = R (TyChan u _) (IsWrite result)
use (ProjectRead prf) with (use prf)
  use (ProjectRead prf) | (R u used result)
    = R (TyChan _ u) (IsRead result)

-- [ EOF ]
