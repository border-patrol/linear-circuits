module Circuits.NetList.Linear.Pretty

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
import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.Common
import public Circuits.Common.Pretty

import Circuits.NetList.Pretty
import Circuits.NetList.Lexer
import Circuits.NetList.Linear.Error
import Circuits.NetList.Linear.AST

import Circuits.NetList.Types

--import Circuits.NetList.Linear.Terms

export
Show AST where
  show (Ref (MkRef span get))
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

  show (Index x d k y)
    = "(Index \{show x} \{show d} \{show k} \{get y})"

  show (Split x y z w)
    = "(Split \{show y} \{show z} \{show w})"

  show (Collect x y z w)
    = "(Collect \{show y} \{show z} \{show w})"

  show (Stop x)
    = "(Stop)"

toNat : IsVar ctxt type -> Nat
toNat (V pos prf) = pos

Show (Project dir) where
  show WRITE = "Write"
  show READ = "Read"



{-
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
-}
-- [ EOF ]
