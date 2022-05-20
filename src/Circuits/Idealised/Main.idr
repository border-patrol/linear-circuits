module Circuits.Idealised.Main

import System
import System.File

import Circuits.Idealised.Core
import Circuits.Idealised
import Circuits.Idealised.Pretty

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
