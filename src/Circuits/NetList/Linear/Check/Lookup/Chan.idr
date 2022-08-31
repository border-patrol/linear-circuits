module Circuits.NetList.Linear.Check.Lookup.Chan

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
IsChan : {is   : List Item}
        -> (key  : String)
        -> (ctxt : Context is)
                -> Type
IsChan str ctxt
  = Exists Item IsChan str ctxt

isChan' : {types : List Item}
       -> (str   : String)
       -> (ctxt  : Context types)
                -> DecInfo (Exists.Error ())
                           (IsChan str ctxt)
isChan'
  = exists (\i => embed (isChan i))


build : {ctxt : Context types}
     -> HoldsAtIndex Item Item (Holds Item IsChan str) ctxt loc
     -> AtIndex (I (TyChan type) (TyChan uin uout)) types loc
     -> (IsChan (I (TyChan type) (TyChan uin uout)) types)
build (Here (H Refl prf)) Here
  = Here Refl prf
build (There _ later) (There x)
  = There (build later x)


namespace Lookup
  export
  isChan : (fc    : FileContext)
        -> {types : List Item}
        -> (str   : String)
        -> (ctxt  : Context types)
                 -> Linear (DPair Ty (API.Result types))
  isChan fc str ctxt with (isChan' str ctxt)
    isChan fc str ctxt | (Yes (E (I (TyChan type) (TyChan uin uout)) item (IC (Val $ I (TyChan type) (TyChan uin uout))) locC locN))
      = do let idx = build locC locN
           pure (TyChan type ** R ctxt (VarChan idx))


    isChan fc str ctxt | (No NotFound _)
      = throwAt fc (NotBound str)
    isChan fc str ctxt | (No (NotSatisfied x) _)
      = throwAt fc PortExpected

-- [ EOF ]
