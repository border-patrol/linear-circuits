module Circuits.NetList.Pretty

import System.File

import Data.String

import Text.Lexer
import Text.Parser

import Toolkit.Data.Whole
import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Toolkit.Data.List.DeBruijn
import Toolkit.Data.List.Occurs.Does
import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Graph.EdgeBounded.HasExactDegree

import Circuits.Common
import Circuits.NetList.Types
import Circuits.NetList.Check

import public Circuits.Common.Pretty

export
Show Direction where
  show INPUT  = "input"
  show OUTPUT = "output"
  show INOUT  = "inout"


export
Show (Types.Cast.Cast f t) where
  show BI = "down"
  show BO = "up"

export
Show (Index f) where
  show (UP _) = "UP"
  show (DOWN _) = "DOWN"

export
Show Gate.Binary.Kind where
  show AND  = "and"
  show IOR  = "or"
  show XOR  = "xor"
  show ANDN = "nand"
  show IORN = "nor"
  show XORN = "xnor"

export
Show Ty where
  show TyUnit         = "()"
  show (TyPort (d,t)) = "TyPort(" <+> show d <+> "," <+> show t <+> ")"
  show TyGate         = "TyGate"
  show (TyChan t)     = "TyChan(" <+> show t <+> ")"

export
Show Check.Error where
  show (Mismatch x y)
    = "Type Mismatch:\n\n"
      <+>
      unlines [unwords ["\tExpected:",show x], unwords ["\tGiven:", show y]]

  show (MismatchD x y)
    = "Type Mismatch:\n\n"
      <+>
      unlines [unwords ["\tExpected:",show x], unwords ["\tGiven:", show y]]


  show (NotBound x)
    = unwords ["Undeclared variable:", x]

  show (VectorExpected)
    = "Vector Expected"

  show (PortChanExpected)
    = "Port or Wire Expected"

  show (PortExpected)
    = "Port Expected"

  show (ErrI msg)
    = "Internal Err: " <+> msg
  show (OOB x y)
    = unwords ["Out of Bounds:" , show x, "is not within", show y]

  show (Err x y) = unwords [show x, show y]

-- [ EOF ]
