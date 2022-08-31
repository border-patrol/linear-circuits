|||
|||
||| Module    : Elab.idr
||| Copyright : (c) Jan de Muijnck-Hughes
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

namespace Full
  export
  lookup : {types : List Item}
        -> (fc   : FileContext)
        -> (str  : String)
        -> (ctxt : Context types)
                -> Linear (DPair Ty (API.Result types))
  lookup fc str ctxt
      = tryCatchOn portFail (isFreePort fc str ctxt)
      $ tryCatchOn gateFail (isGate fc str ctxt)
      $                     (isChan fc str ctxt)
    where

      portFail : Linear.Error -> Bool
      portFail (TyCheck (NotBound str)) = True
      portFail (TyCheck (LinearityError strs)) = True
      portFail _ = False

      gateFail : Linear.Error -> Bool
      gateFail (TyCheck (NotBound str)) = True
      gateFail _ = False


namespace Partial
  buildHow : (fc : FileContext) -> (dir : Direction) -> Linear (Project dir)
  buildHow fc INPUT
    = pure READ
  buildHow fc OUTPUT
    = pure WRITE
  buildHow fc INOUT
    = throwAt fc (ErrI "Projecting INOUT")

  portFail' : Linear.Error -> Bool
  portFail' (TyCheck (NotBound str)) = True
  portFail' (TyCheck (LinearityError strs)) = True
  portFail' (TyCheck PortChanExpected) = True
  portFail' _ = False

  export
  lookup : {types : List Item}
        -> (fc    : FileContext)
        -> (ed    : Direction)
        -> (idx   : List Nat)
        -> (str   : String)
        -> (ctxt  : Context types)
                -> Linear (DPair Ty (API.Result types))
  lookup fc ed idx str ctxt
      = tryCatchOn portFail' (isFreePortAt fc     idx str ctxt)
      $                      (do how <- buildHow fc ed
                                 canProjectAt fc how idx str ctxt)


-- [ EOF ]
