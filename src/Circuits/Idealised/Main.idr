module Circuits.Idealised.Main

import System
import System.File

import Data.String
import Data.List1

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Toolkit.Data.List.Occurs.Does
import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Graph.EdgeBounded.HasExactDegree



import Circuits.Idealised.Types
import Circuits.Idealised.Terms
import Circuits.Idealised.AST
import Circuits.Idealised.Lexer
import Circuits.Idealised.Parser
import Circuits.Idealised.Check
import Circuits.Idealised.Interp

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

export
Show (Vertex String) where
  show (Node d k j i) = show k <+> " [label=\"" <+> show (j,i) <+> " " <+> d <+> "\"];"
  show (Leaf d x k j) = show k <+> " [label=\"" <+> withFlow x j <+> " " <+> d <+> "\"];"
    where withFlow : Flow -> Nat -> String
          withFlow f k = show f <+> "(" <+> show k <+>")"

export
showGraph : Graph String -> String
showGraph (MkGraph nodes edges)
    = unlines $ ["digraph G {"]
                ++
                  map show nodes
                ++
                  map (\(x,y) => unwords ["\t" <+> show x, "->", show y <+> ";"]) edges
                ++
                ["}"]

export
Show DegreeType where
  show I = "IN"
  show O = "OUT"

export
showErr : (Graph String, HasExactDegree.Error String)  -> String
showErr (g, MkError vertex kind (MkError vertexID k values))
 = unlines [showGraph g
           , "//because:"
           , "// Vertex " <+> show (ident vertex)
           , "//  has expected degree " <+> show k <+> " " <+> show (values.expected)
           , "//  but we found degree " <+> show k <+> " " <+> show (values.found)
           ]

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
