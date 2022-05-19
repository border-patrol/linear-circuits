module Circuits.Common.Pretty

import System.File

import Data.String

import Toolkit.Data.List.Occurs.Does
import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Graph.EdgeBounded.HasExactDegree

import Text.Lexer
import Text.Parser

import Toolkit.Data.Whole
import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Circuits.Common

export
Show Usage where
  show USED = "Used"
  show FREE = "Free"

export
Show DType where
  show LOGIC = "logic"
  show (BVECT n type) = show type <+> concat ["[", show n, "]"]


export
[circuitspf] Show a => Show (ParseFailure a) where
  show err
    = trim $ unlines [show (location err), (error err)]

export
[circuitspe] Show a => Show (ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines (forget (map (show @{circuitspf}) err))

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


-- [ EOF ]
