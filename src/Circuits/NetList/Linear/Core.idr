||| The Core Computation Context.
|||
||| `TheRug` is defined in the toolkit. Here we establish the synonyms
||| required for `Idealised`.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Core

import        System

import        Data.String

import public Toolkit.TheRug
import        Toolkit.System

import public Circuits.NetList.Linear.Error
import public Circuits.Common.Pretty

import Circuits.Common.Lexer
import Circuits.Common.Parser

%default total

public export
%inline
Linear : Type -> Type
Linear = TheRug NetList.Linear.Error


namespace NetList
  namespace Linear

    %inline
    whenErr : (msg : NetList.Linear.Error)
                  -> IO ()
    whenErr err
      = do putStrLn (show err)
           exitWith (ExitFailure 1)

    %inline
    whenOK : a -> IO ()
    whenOK _ = pure ()

    export
    run : (prog : Linear a)
               -> IO ()
    run = run whenErr whenOK

-- [ EOF ]
