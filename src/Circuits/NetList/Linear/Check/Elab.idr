|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Check.Elab

import Toolkit.Decidable.Do

import Data.Nat
import Data.String
import Data.Fin

import Toolkit.Data.DList
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

import Circuits.NetList.Linear.Check.Elab.Helper
import Circuits.NetList.Linear.Check.Elab.Project
import Circuits.NetList.Linear.Check.Lookup.ProjectAt
import Circuits.NetList.Linear.Check.Lookup.PortAt

%default total

||| Return the datatype associated with the term.
|||
||| Throws an exception if gate or unit encountered.
export
getDataType : (fc   : FileContext)
           -> (term : (type ** API.Result ctxt type))
                   -> Linear DType

getDataType fc ((TyPort (x, dtype)) ** tm)
  = pure dtype

getDataType fc ((TyChan dtype) ** tm)
  = pure dtype

getDataType fc (_ ** tm)
  = throwAt fc PortChanExpected

||| Check if result is a port in the expected direction and type..
export
checkPort : (fc    : FileContext)
         -> (exdir : Direction)
         -> (expty : DType)
         -> (term  : (type ** API.Result ctxt type))
                  -> Linear (API.Result ctxt
                                        (TyPort (exdir,expty)))

checkPort fc ed et ((TyPort (_,gt)) ** tm)
  = do Refl <- embedAt fc
                       (MismatchD et gt)
                       (decEq et gt)

       portCast fc ed tm

-- [ NOTE ] Channels need projecting

-- [ NOTE ]
--
-- READ implies INPUT
checkPort fc INPUT et ((TyChan x) ** (R new (VarChan prf)))
  = do Refl <- embedAt fc (MismatchD et x)
                          (decEq     et x)
       idx <- embedAt fc
                      (const $ ErrI "Linearity error on projection R")
                      (canProject READ prf)

       let (newItems ** prfU) = useChannel _ idx
       let new = update new prfU
       pure (R new (Project READ idx prfU))

-- [ NOTE ]
--
-- OUTPUT implies write
checkPort fc OUTPUT et ((TyChan x) ** (R new (VarChan prf)))
  = do Refl <- embedAt fc (MismatchD et x)
                          (decEq     et x)

       idx <- embedAt fc
                      (const $ ErrI "Linearity error on projection W")
                      (canProject WRITE prf)

       let (newItems ** prfU) = useChannel _ idx
       let new = update new prfU
       pure (R new (Project WRITE idx prfU))

-- [ NOTE ]
--
-- INOUT Chan's impossible.
checkPort fc INOUT _ ((TyChan _) ** _)
  = throwAt fc (ErrI "INOUT CHAN not expected")


-- [ NOTE ]
--
-- Type Gates/Unit not expected.
--
checkPort fc exdir expty (type ** _)
  = throwAt fc (Mismatch (TyPort (exdir,expty))
                          type)


-- [ EOF ]
