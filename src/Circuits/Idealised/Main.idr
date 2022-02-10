module Circuits.Idealised.Main

import System
import System.File

import Circuits.Idealised
import Circuits.Idealised.Pretty

main : IO Unit
main
  = do putStrLn "// LOG : Starting Idealised Linear "
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
