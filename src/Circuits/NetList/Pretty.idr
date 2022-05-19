module Circuits.NetList.Pretty

import System.File

import Data.String

import Data.Fin

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
import Circuits.NetList.AST
import Circuits.NetList.Types

import Circuits.NetList.Terms
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
Show AST where
  show (Var (MkRef span get))
    = "(Var \{get})"

  show (Port x y z (MkRef span get) scope)
    = "(Port \{show y} \{show z} \{show get} \{show scope})"

  show (Wire x y (MkRef span get) scope)
    = "(Wire \{show y} \{show get} \{show scope})"

  show (GateDecl x (MkRef span get) z scope)
    = "(Gate \{show get} \{show z} \{show scope})"

  show (Shim x y z)
    = "(Shim \{show y} \{show z})"

  show (Assign x y z w)
    = "(Assign \{show y} \{show z} \{show w})"

  show (Mux x y z w v)
    = "(Mux \{show y} \{show z} \{show w} \{show v})"

  show (GateU x y z w)
    = "(GateU \{show y} \{show z} \{show w})"

  show (GateB x y z w v)
    = "(GateB \{show y} \{show z} \{show w} \{show v})"

  show (Index x k y)
    = "(Index \{show k} \{show y})"

  show (Split x y z w)
    = "(Split \{show y} \{show z} \{show w})"

  show (Collect x y z w)
    = "(Collect \{show y} \{show z} \{show w})"

  show (Stop x)
    = "(Stop)"

toNat : Elem x xs -> Nat
toNat Here = Z
toNat (There y) = S (toNat y)

Show (Project dir) where
  show WRITE = "Write"
  show READ = "Read"

export
Show (Term ctxt type) where
  show (Var prf)
    = "(Var \{show (toNat prf)})"

  show (Port flow dtype body)
    = "(Port \{show flow} \{show dtype} \{show body})"

  show (Wire x body)
    = "(Wire \{show x} \{show body})"

  show (GateDecl g body)
    = "(Gate \{show g} \{show body})"

  show Stop
    = "Stop"

  show (Assign i o body)
    = "(Assign \{show i} <- \{show o} \{show body})"

  show (Index idir what idx)
    = "(Index \{show idir} \{show what} \{show idx})"

  show (Mux o c l r)
    = "(Mux \{show o} \{show c} \{show l} \{show r})"

  show (GateB x o l r)
    = "(GateB \{show x} \{show o} \{show l} \{show r})"

  show (GateU x o i)
    = "(GateU \{show x} \{show o} \{show i})"

  show (Collect o l r)
    = "(Collect \{show o} \{show l} \{show r})"

  show (Split l r i)
    = "(Split \{show l} \{show r} \{show i})"

  show (Project how what)
    = "(Project \{show how} \{show what})"

  show (Cast dir what)
    = "(Cast \{show dir} \{show what})"


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
