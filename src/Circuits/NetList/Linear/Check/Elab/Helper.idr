module Circuits.NetList.Linear.Check.Elab.Helper

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


||| Need to make sure that the indices are in the correct direction.
rewriteTerm : (c  : Cast flow expected)
           -> (i  : Index INOUT)
           -> (tm : API.Result ctxt (TyPort (flow,type)))
                 -> API.Result ctxt (TyPort (flow,type))

-- [ NOTE ] Ports kept the same.
rewriteTerm _ _ (R new (FreePort prf use))
  = R new (FreePort prf use)

-- [ NOTE ] Indices are what we care about.
rewriteTerm BI (UP UB) (R new (Index _ idx prf use o))
  = R new (Index (UP UB) idx prf use o)

rewriteTerm BI (DOWN DB) (R new (Index _ idx prf use o))
  = R new (Index (DOWN DB) idx prf use o)

rewriteTerm BO (UP UB) (R new (Index _ idx prf use o))
  = R new (Index (UP UB) idx prf use o)

rewriteTerm BO (DOWN DB) (R new (Index _ idx prf use o))
  = R new (Index (DOWN DB) idx prf use o)

-- [ NOTE ] Impossible Cases
rewriteTerm BI _ (R _ (Cast BI _)) impossible
rewriteTerm BI _ (R _ (Cast BO _)) impossible

rewriteTerm BO _ (R _ (Cast BI _)) impossible
rewriteTerm BO _ (R _ (Cast BO _)) impossible

rewriteTerm BO _ (R _ (Project WRITE _ _)) impossible
rewriteTerm BI _ (R _ (Project WRITE _ _)) impossible

rewriteTerm BO _ (R _ (Project READ _ _)) impossible
rewriteTerm BI _ (R _ (Project READ _ _)) impossible

rewriteTerm BO _ (R _ (ProjectAt WRITE _ _ _ _)) impossible
rewriteTerm BI _ (R _ (ProjectAt WRITE _ _ _ _)) impossible
rewriteTerm BO _ (R _ (ProjectAt READ  _ _ _ _)) impossible
rewriteTerm BI _ (R _ (ProjectAt READ  _ _ _ _)) impossible


||| When casting we finally know which direction indexing should go,
||| so lets fix that.
shouldCast : {type : DType}
          -> (given,expected : Direction)
          -> (term : API.Result ctxt (TyPort (given,type)))
                  -> Dec ( Cast given expected
                         , API.Result ctxt (TyPort (expected,type))
                         )
shouldCast given expected term with (Cast.cast given expected)
  shouldCast INOUT INPUT term | (Yes BI) with (dirFromCast BI)
    shouldCast INOUT INPUT term | (Yes BI) | idir with (rewriteTerm BI idir term)
      shouldCast INOUT INPUT term | (Yes BI) | idir | (R new x)
        = Yes (BI, R new (Cast BI x))

  shouldCast INOUT OUTPUT term | (Yes BO) with (dirFromCast BO)
    shouldCast INOUT OUTPUT term | (Yes BO) | idir with (rewriteTerm BO idir term)
      shouldCast INOUT OUTPUT term | (Yes BO) | idir | (R new x)
        = Yes (BO, R new (Cast BO x))
  shouldCast given expected term | (No no)
    = No (\(prf, t) => no prf)

||| If the port is INOUT then cast, otherwise leave it alone if the
||| directions match.
export
portCast : {type     : DType}
        -> {given    : Direction}
        -> (fc       : FileContext)
        -> (expected : Direction)
        -> (term     :         API.Result ctxt (TyPort (given,   type)))
                    -> Linear (API.Result ctxt (TyPort (expected,type)))

portCast {type} {given} fc expected term with (shouldCast given expected term)
  portCast {type = type} {given = given} fc expected term | (Yes (prf, tm))
    = pure tm

  portCast {type = type} {given = given} fc expected term | (No no)
    = do Refl <- embedAt fc
                         (Mismatch (TyPort (expected, type))
                                   (TyPort (given,    type))
                         )
                         (decEq given expected)
         pure term


-- [ EOF ]
