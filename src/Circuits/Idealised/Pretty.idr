module Circuits.Idealised.Pretty

import System.File

import Data.String


import Text.Lexer
import Text.Parser

import Toolkit.Data.Whole
import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Toolkit.DeBruijn.Context

import public Circuits.Common.Pretty
import        Circuits.Idealised.Types
import        Circuits.Idealised.Check

%default total

export
Show Direction where
  show INPUT  = "input"
  show OUTPUT = "output"

export
Show Ty where
  show TyUnit = "()"
  show (TyPort (d,t)) = concat ["TyPort(", show d, ",", show t, ")"]
  show TyGate = "TyGate"

export
Show GateKind where
  show AND  = "and"
  show IOR  = "or"
  show XOR  = "xor"
  show ANDN = "nand"
  show IORN = "nor"
  show XORN = "xnor"
  show JOIN = "join"

showEnv : Context type -> String
showEnv [] = ""
showEnv ((I name (type, FREE)) :: rest)
  = name <+> " : " <+> show type <+> "\n" <+> (showEnv rest)
showEnv ((I name (type, USED)) :: rest) = showEnv rest

export
Show FailingEdgeCase where
  show (InvalidSplit p s l r) = "Pivot (" <+> show p <+> ") is wrong do not add up: " <+> unwords [show s, "!= 1 + ", show l, "+", show r]
  show (InvalidEdge  s l r) = "Indices do not add up: " <+> unwords [show s, "= 1 + ", show l, "+", show r]

export
Show Check.Error where
  show (Mismatch x y)
    = "Type Mismatch:\n\n"
      <+> unlines [unwords ["\tExpected:",show x], unwords ["\tGiven:", show y]]

  show (MismatchGate x y)
    = "Type Mismatch:\n\n"
     <+> unlines [unwords ["\tExpected:",show x], unwords ["\tGiven:", show y]]

  show (ElemFail (NotSatisfied (NotFound x)))
    = unwords ["Undeclared variable::", x]

  show (ElemFail (NotSatisfied (IsUsed x)))
    = unwords ["Port is used:", x]

  show (ElemFail NotFound)
    = "Port not found."

  show (NotEdgeCase r)  = "Not an edge case:\n\n" <+> show r
  show (PortExpected INPUT) = "Expected an Input Port"
  show (PortExpected OUTPUT) = "Expected an Output Port"
  show (LinearityError env) = "Dangling Ports:\n\n" <+> showEnv env
  show (VectorExpected) = "Vector Expected"
  show (VectorTooShort) = "Output Vector must be a length greater or equal to two."
  show (VectorSizeMismatch o a b)
    = unlines [ "Output Vector and input are wrong sizes:"
              , unwords ["\t" <+> show o, "!=", show a, "+", show b]]
  show (Err x y) = unwords [show x, show y]


-- [ EOF ]
