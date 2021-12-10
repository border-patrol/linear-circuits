module Circuits.NetList.Main

import System
import System.File

import Data.String
import Data.List1

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import EdgeBoundedGraph

import Circuits.NetList.Types
import Circuits.NetList.Terms
import Circuits.NetList.AST
import Circuits.NetList.Lexer
import Circuits.NetList.Parser

export
Show a => Show (ParseFailure a) where
  show err
    = trim $ unlines [show (location err), (error err)]

export
Show a => Show (ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines (forget (map show err))

  show (LError (MkLexFail l i))
    = trim $ unlines [show l, show i]


main : IO Unit
main
  = do putStrLn "// LOG : Starting NetList "
       args <- getArgs

       case args of
         [x,y] => do Right ast <- fromFile y
                       | Left err => do putStrLn "// LOG : Failure Parsing"
                                        printLn err
                                        exitFailure

                     exitSuccess
         _ => do putStrLn "need at least a file name"
                 exitFailure


-- [ EOF ]
