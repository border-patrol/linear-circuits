module Circuits.NetList.Linear.Check.Lookup.Gate

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
IsGate : {is   : List Item}
        -> (key  : String)
        -> (ctxt : Context is)
                -> Type
IsGate str ctxt
  = Exists Item IsGate str ctxt

isGate' : {types : List Item}
       -> (str   : String)
       -> (ctxt  : Context types)
                -> DecInfo (Exists.Error ())
                           (IsGate str ctxt)
isGate'
  = exists (\i => embed (isGate i))


build : {ctxt : Context types}
     -> HoldsAtIndex Item Item (Holds Item IsGate str) ctxt loc
     -> AtIndex (I TyGate TyGate) types loc
     -> (IsGate (I TyGate TyGate) types)
build (Here (H Refl prf)) Here
  = Here Refl prf
build (There _ later) (There x)
  = There (build later x)


namespace Lookup
  export
  isGate : (fc    : FileContext)
        -> {types : List Item}
        -> (str   : String)
        -> (ctxt  : Context types)
                 -> Linear (DPair Ty (API.Result types))
  isGate fc str ctxt with (isGate' str ctxt)
    isGate fc str ctxt | (Yes (E (I TyGate TyGate) item IG locC locN))
      = do let idx = build locC locN
           pure (TyGate ** R ctxt (VarGate idx))


    isGate fc str ctxt | (No NotFound _)
      = throwAt fc (NotBound str)
    isGate fc str ctxt | (No (NotSatisfied x) _)
      = throwAt fc PortChanExpected


-- [ EOF ]
