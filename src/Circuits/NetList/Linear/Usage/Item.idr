module Circuits.NetList.Linear.Usage.Item

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
import Circuits.NetList.Linear.Usage.TermType.Use.Port
import Circuits.NetList.Linear.Usage.TermType.Use.Channel

%default total

namespace Usage
  public export
  record Item where
    constructor I
    getType : Ty
    getUsage : Usage getType


namespace Port
  public export
  data FreePort : (flow : Direction)
               -> (type : DType)
               -> (item : Item)
                        -> Type
    where
      FP : (u : Usage type) -> (prf : IsFree type u) -> FreePort flow type (I (TyPort (flow, type)) (TyPort u))

  public export
  freePort : (flow : Direction)
          -> (type : DType)
                  -> DPair Item (FreePort flow type)
  freePort flow type with (init type)
    freePort flow type | (MkDPair u prf)
      = MkDPair (I (TyPort (flow, type)) (TyPort u)) (FP u prf)

  public export
  data IsFreePort : (item : Item)
                         -> Type
    where
      IFP : (usage : Usage (TyPort (flow, type)))
         -> (prf   : IsFree        (TyPort (flow, type)) usage)
                  -> IsFreePort (I (TyPort (flow, type)) usage)

  Uninhabited (IsFreePort (I TyGate ug)) where
    uninhabited (IFP usage prf) impossible

  Uninhabited (IsFreePort (I (TyChan type) uc)) where
    uninhabited (IFP usage prf) impossible

  Uninhabited (IsFreePort (I TyUnit uu)) where
    uninhabited (IFP usage prf) impossible

  export
  isFreePort : (item : Item) -> Dec (IsFreePort item)
  isFreePort (I (TyPort x) getUsage) with (isFree getUsage)
    isFreePort (I (TyPort (x, y)) getUsage) | (Yes prf)
      = Yes (IFP getUsage prf)
    isFreePort (I (TyPort (x,y)) getUsage) | (No contra)
      = No (\(IFP getUsage pu) => contra pu)

  isFreePort (I TyUnit getUsage)
    = No absurd

  isFreePort (I (TyChan x) getUsage)
    = No absurd

  isFreePort (I TyGate getUsage)
    = No absurd


public export
data FreeChan : (type : DType) -> (item : Item) -> Type where
  FC : (u : Usage type) -> (prf : IsFree type u) -> FreeChan type (I (TyChan type) (TyChan u u))


public export
freeChan : (type : DType) -> DPair Item (FreeChan type)
freeChan type with (init type)
  freeChan type | (MkDPair u prf)
    = MkDPair (I (TyChan type) (TyChan u u)) (FC u prf)

-- I (TyPort (flow,type)) ?as)

public export
data CanStop : Item -> Type where
  StopG : CanStop (I TyGate TyGate)
  StopU : CanStop (I TyUnit TyUnit)

  StopP : (prf : IsUsed     (TyPort (flow,dtype)) u)
              -> CanStop (I (TyPort (flow,dtype)) u)

  StopC : (prf : IsUsed     (TyChan type) u)
              -> CanStop (I (TyChan type) u)


portIsFree : (IsUsed (TyPort x) u -> Void) -> CanStop (I (TyPort x) u) -> Void
portIsFree f (StopP prf) = f prf

chanOutIsFree : (IsUsed x eout -> Void) -> CanStop (I (TyChan x) (TyChan ein eout)) -> Void
chanOutIsFree f (StopC (UsedC uin uou)) = f uou

chanInIsFree : (IsUsed x ein -> Void) -> CanStop (I (TyChan x) (TyChan ein eout)) -> Void
chanInIsFree f (StopC (UsedC uin uou)) = f uin

export
canStop : (i : Item) -> Dec (CanStop i)
canStop (I TyUnit TyUnit)
  = Yes StopU

canStop (I (TyPort x) u) with (isUsed u)
  canStop (I (TyPort (flow, type)) (TyPort u)) | (Yes (UsedP y))
    = Yes (StopP (UsedP y))

  canStop (I (TyPort x) u) | (No contra)
    = No (portIsFree contra)

canStop (I (TyChan x) (TyChan ein eout)) with (isUsed ein)
  canStop (I (TyChan x) (TyChan ein eout)) | (Yes prfIN) with (isUsed eout)
    canStop (I (TyChan x) (TyChan ein eout)) | (Yes prfIN) | (Yes prfOUT)
      = Yes (StopC (UsedC prfIN prfOUT))

    canStop (I (TyChan x) (TyChan ein eout)) | (Yes prfIN) | (No contra)
      = No (chanOutIsFree contra)

  canStop (I (TyChan x) (TyChan ein eout)) | (No contra)
    = No (chanInIsFree contra)

canStop (I TyGate TyGate)
  = Yes StopG

-- [ EOF ]
