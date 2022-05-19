module Circuits.Idealised.Main

import System
import System.File

import Circuits.Idealised.Core
import Circuits.Idealised
import Circuits.Idealised.Pretty

{-
main : IO Unit
main
  = do
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

-}

processArgs : List String -> IO String
processArgs [exe,fname] = pure fname
processArgs _
  = do putStrLn "Exactly one file at a time."
       exitFailure

idealised : (fname : String)
                  -> Idealised ()

idealised fname
  = do putStrLn "// LOG : Starting Idealised Linear"

       ast <- fromFile fname

       log "// LOG : Parsing Successful"

       term <- Design.check ast

       log "// LOG : Type Checking Complete"

       prf <- isSound term

       log "// LOG : Soundness Check Complete"

       putStrLn ((showGraph . fst . getGraph) prf)

       log "// LOG : BYE"

main : IO ()
main
  = do fname <- processArgs !getArgs
       run (idealised fname)

-- [ EOF ]
