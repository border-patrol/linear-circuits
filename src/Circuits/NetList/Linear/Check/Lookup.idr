|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Check.Lookup

import Toolkit.Decidable.Do

import Data.Nat
import Data.String
import Data.Fin

import Toolkit.Data.Whole
import Toolkit.Data.Location

import Toolkit.Data.Whole

import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.NetList.Types
import Circuits.NetList.Terms

import Circuits.NetList.Linear.Core
import Circuits.NetList.Linear.Check.API
import Circuits.NetList.Linear.Usage
import Circuits.NetList.Linear.Terms

import Circuits.NetList.Linear.Check.Lookup.Port
import Circuits.NetList.Linear.Check.Lookup.Gate
import Circuits.NetList.Linear.Check.Lookup.Chan

import Circuits.NetList.Linear.Check.Lookup.PortAt
import Circuits.NetList.Linear.Check.Lookup.ProjectAt

%default total

%inline
whenExcept : Linear.Error -> Maybe Linear.Error
whenExcept e@(TyCheck (NotBound str)) = Just e
whenExcept e@(TyCheck (LinearityError strs)) = Just e
whenExcept e@(TyCheck (Err fc e'))           = assert_total $ maybe Nothing (const $ Just e) (whenExcept (TyCheck e'))

whenExcept _ = Nothing

namespace Full
  export
  lookup : {types : List Item}
        -> (fc   : FileContext)
        -> (str  : String)
        -> (ctxt : Context types)
                -> Linear (DPair Ty (API.Result types))
  lookup fc str ctxt
      = handleWith whenExcept (isGate fc str ctxt)
      $ handleWith whenExcept (isChan fc str ctxt)
                              (isFreePort fc str ctxt)

namespace Partial
  %inline
  buildHow : (fc : FileContext) -> (dir : Direction) -> Linear (Project dir)
  buildHow fc INPUT
    = pure READ
  buildHow fc OUTPUT
    = pure WRITE
  buildHow fc INOUT
    = throwAt fc (ErrI "Projecting INOUT")


  whenExcept : Linear.Error -> Maybe Linear.Error
  whenExcept e@(TyCheck (NotBound str))        = Just e
  whenExcept e@(TyCheck (LinearityError strs)) = Just e
  whenExcept e@(TyCheck (IOOB xs ys))          = Just e
  whenExcept e@(TyCheck (OOB xs ys))           = Just e
  whenExcept e@(TyCheck (Err fc e'))           = assert_total $ maybe Nothing (const $ Just e) (Partial.whenExcept (TyCheck e'))
  whenExcept _ = Nothing

  export
  lookup : {types : List Item}
        -> (fc    : FileContext)
        -> (ed    : Direction)
        -> (idx   : List Nat)
        -> (str   : String)
        -> (ctxt  : Context types)
                -> Linear (DPair Ty (API.Result types))
  lookup fc ed idx str ctxt

    = handleWith (Partial.whenExcept)
                 (isFreePortAt fc idx str ctxt)
                 (do how <- buildHow fc ed
                     canProjectAt fc how idx str ctxt)


-- [ EOF ]
