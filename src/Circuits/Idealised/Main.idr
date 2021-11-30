module Circuits.Idealised.Main

import System

import Data.List1

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import EdgeBoundedGraph
import Circuits.Types

import Circuits.Idealised
import Circuits.Idealised.AST
import Circuits.Idealised.Lexer
import Circuits.Idealised.Parser
import Circuits.Idealised.Check
import Circuits.Idealised.Interp


main : IO Unit
main
  = do putStrLn "LOG : Starting Idealised Linear "
       args <- getArgs

       case args of
         [x,y] => do Right ast <- fromFile y
                       | Left err => do putStrLn "Failure AST"
                                        exitFailure
                     Right term <- typeCheckIO ast
                       | Left err => do putStrLn "Failure TyCheck"
                                        printLn err
                                        exitFailure
                     Just (g ** D g prf) <- runIO term
                       | Nothing => do putStrLn "Failure Interp"
                                       exitFailure
                     exitSuccess
         _ => do putStrLn "need at least a file name"
                 exitFailure
