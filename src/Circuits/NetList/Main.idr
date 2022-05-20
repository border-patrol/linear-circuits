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

netlist : (fname : String)
                -> NetList ()
netlist fname
  = do putStrLn "// LOG : Starting NetList "

       ast <- fromFile fname

       log "// \{show ast}"

       log "// LOG : Parsing Successful"

       term <- Design.check ast

       log "// \{show term}"

       log "// LOG : Type Checking Complete"

       prf <- isSound term

       log "// LOG : Soundness Check Complete"

       putStrLn ((showGraph . fst . getGraph) prf)

       log "// LOG : BYE"

main : IO Unit
main
  = do fname <- processArgs !getArgs
       run (netlist fname)

-- [ EOF ]
