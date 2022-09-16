||| The Core Computation Context.
|||
||| `TheRug` is defined in the toolkit. Here we establish the synonyms
||| required for `Idealised`.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Core

import        System

import        Data.String

import public Toolkit.TheRug
import        Toolkit.System

import public Circuits.NetList.Error
import        Circuits.NetList.Pretty

%default total

public export
%inline
NetList : Type -> Type
NetList = TheRug NetList.Error

namespace NetList

  %inline
  whenErr : (msg : NetList.Error)
                -> IO ()
  whenErr err
    = do putStrLn (show err)
         exitWith (ExitFailure 1)

  %inline
  whenOK : a -> IO ()
  whenOK _ = pure ()

  export
  run : (prog : NetList a)
             -> IO ()
  run = run whenErr whenOK

-- [ EOF ]
