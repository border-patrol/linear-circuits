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

import Circuits.NetList.Types
import Circuits.NetList.Terms
import Circuits.NetList.AST
import Circuits.NetList.Lexer
import Circuits.NetList.Parser
import Circuits.NetList.Check
import Circuits.NetList.Interp

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

Show (Term ctxt t) where
  show (Var x)
      = unwords ["(var", showElem x <+> ")"]
    where
      toNat : Elem ty xs -> Nat
      toNat Here = Z
      toNat (There x) = S (toNat x)

      showElem : Elem ty xs -> String
      showElem =  (show . toNat)

  show (Port flow x body)
    = unwords ["(port", show (flow,x), show body <+> ")"]

  show (Wire x body)
    = unwords ["(wire", show x, show body <+> ")"]


  show (GateDecl g body)
    = unwords ["(gate", show g, show body <+> ")"]

  show (Assign i o body)
    = unwords ["(assign", show i, show o, show body <+> ")"]

  show Stop = ""

  show (Index dir x y)
    = show x <+> "[" <+> show y <+> "](" <+> show dir <+>")"

  show (Mux o c l r)
    = unwords ["(mux" <+> show o, show c, show l, show r <+> ")"]

  show (GateB x o l r)
    = unwords ["(" <+> show x, show o, show l, show r <+> ")"]

  show (GateU x o i)
    = unwords ["(" <+> show x, show o, show i <+> ")"]

  show (Project WRITE y)
    = unwords ["(project write", show y <+> ")"]

  show (Project READ y)
    = unwords ["(project read", show y <+> ")"]

  show (Cast x y)
    = unwords ["(cast", show y <+> ")"]

  show (Collect o a b)
    = unwords ["(collect", show o, show a, show b <+> ")"]

  show (Split a b i)
    = unwords ["(split", show a, show b, show i <+> ")"]

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
