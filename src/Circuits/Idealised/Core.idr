||| The Core Computation Context.
|||
||| `TheRug` is defined in the toolkit. Here we establish the synonyms
||| required for `Idealised`.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.Idealised.Core

import        System

import        Data.String

import public Toolkit.TheRug
import        Toolkit.System

import public Circuits.Idealised.Error
import        Circuits.Idealised.Pretty

%default total

public export
%inline
Idealised : Type -> Type
Idealised = TheRug Idealised.Error

namespace Idealised

  %inline
  whenErr : (msg : Idealised.Error)
                -> IO ()
  whenErr err
    = do putStrLn (show err)
         exitWith (ExitFailure 1)

  %inline
  whenOK : a -> IO ()
  whenOK _ = pure ()

  export
  run : (prog : Idealised a)
             -> IO ()
  run = run whenErr whenOK

-- [ EOF ]
