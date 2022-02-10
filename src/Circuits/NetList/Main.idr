module Circuits.NetList.Main

import System
import System.File

import Data.String
import Data.Fin
import Data.List.Elem
import Data.List1

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Graph.EdgeBounded.HasExactDegree
import Toolkit.Data.List.Occurs.Does

import Circuits.NetList
import Circuits.NetList.Pretty

main : IO Unit
main
  = do putStrLn "// LOG : Starting NetList "
       args <- getArgs

       case args of
         [x,y] => do Right ast <- fromFile y
                       | Left err => do putStrLn "// LOG : Failure Parsing"
                                        printLn err
                                        exitFailure

                     Right term <- typeCheckIO ast
                       | Left err => do putStrLn "// LOG : Failure Type Checking"
                                        printLn err
                                        exitFailure
                     Right res <- runIO term
                       | Left err => do putStrLn "// LOG : Failure Interpreting"
                                        putStrLn (showErr err)
                                        exitFailure
                     putStrLn ((showGraph . fst . getGraph) res)
                     exitSuccess
         _ => do putStrLn "need at least a file name"
                 exitFailure


-- [ EOF ]
