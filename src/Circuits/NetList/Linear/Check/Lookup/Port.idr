module Circuits.NetList.Linear.Check.Lookup.Port

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List.Elem
import Data.List.Quantifiers
import Data.DPair

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Views

import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Whole
import Toolkit.Data.Location
import Toolkit.Data.DList

import Toolkit.Data.List.AtIndex

import Toolkit.Data.DList.AtIndex

import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.NetList.Types
import Circuits.NetList.Linear.Core
import Circuits.NetList.Linear.Usage
import Circuits.NetList.Linear.Terms

import Circuits.NetList.Linear.Check.API

%default total

public export
FreePort : {is   : List Item}
        -> (key  : String)
        -> (ctxt : Context is)
                -> Type
FreePort str ctxt
  = Exists Item IsFree str ctxt


isFreePort' : {types : List Item}
          -> (str  : String)
          -> (ctxt : Context types)
                  -> DecInfo (Exists.Error (DPair Item IsFreeNot))
                             (FreePort str ctxt)
isFreePort'
  = exists (\i => transForm (isFree i))

  where
    transForm : {i : _} -> DecInfo (IsFreeNot i)          (IsFree i)
         -> DecInfo (DPair Item IsFreeNot) (IsFree i)
    transForm (Yes prfWhy) = Yes prfWhy
    transForm (No msgWhyNot prfWhyNot)
      = No (_ ** msgWhyNot) prfWhyNot

update : {curr, next : List Item}
      -> {idx  : IsFreePort i curr}
      -> (ctxt : Context curr)
      -> (use  : UsePort curr idx next)
              -> Context next
update {curr = (i :: xs)} {next = (y :: xs)} ((I name i) :: rest) (UpdateHere use)
  = I name y :: rest
update {curr = (x :: xs)} {next = (x :: ys)} (h :: t) (UpdateThere rest)
  = h :: update t rest

build : {ctxt : Context types}
     -> HoldsAtIndex Item Item (Holds Item IsFree str) ctxt loc
     -> AtIndex (I (TyPort (flow, type)) (TyPort usage)) types loc
     -> (IsFreePort (I (TyPort (flow, type)) (TyPort usage)) types)
build (Here (H Refl prf)) Here
  = Here Refl prf
build (There urgh later) (There x)
  = There (build later x)



namespace Lookup
  export
  isFreePort : (fc    : FileContext)
            -> {types : List Item}
            -> (str   : String)
            -> (ctxt  : Context types)
                     -> Linear (DPair Ty (API.Result types))
  isFreePort {types} fc str curr with (isFreePort' str curr)
    isFreePort {types = types} fc str curr | (Yes (E (I (TyPort (flow, type)) (TyPort usage)) item (Free prf) locC locN))
      = do let idx = build locC locN
           let (new ** prfU) = usePort _ idx
           let next = update curr prfU
           pure (_ ** R next (FreePort idx prfU))


    isFreePort {types = types} fc str curr | (No NotFound _)
      = throwAt fc (NotBound str)
    isFreePort {types = types} fc str curr | (No (NotSatisfied ((I (TyPort x) u) ** p)) _)
      = throwAt fc (LinearityError ["\{str} := \{show u}"])
    isFreePort {types = types} fc str curr | (No (NotSatisfied ((I _ _) ** p)) _)
      = throwAt fc PortExpected

-- [ EOF ]
