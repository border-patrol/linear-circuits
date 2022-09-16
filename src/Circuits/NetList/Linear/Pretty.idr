|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
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

import Circuits.NetList.Lexer
import Circuits.NetList.Linear.Error
import Circuits.NetList.Linear.AST
import Circuits.NetList.Linear.Usage
import Circuits.NetList.Linear.Terms
import Circuits.NetList.Types

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

--toNat : IsVar ctxt type -> Nat
--toNat (V pos prf) = pos

toNat : Elem p x xs -> Nat
toNat (Here prfSame prfSat) = 0
toNat (There rest) = toNat rest


export
Show (Term i type o) where
  show (FreePort prf use)
    = "(VarPort \{show (toNat prf)}})"

  show (VarGate prf)
    = "(VarGate \{show (toNat prf)})"

  show (VarChan prf)
    = "(VarChan \{show (toNat prf)})"

  show (Port flow x urgh body)
    = "(Port \{show flow} \{show x} \{show body})"

  show (Wire x urgh body)
    = "(Wire \{show x} \{show body})"

  show (Gate gate body)
    = "(Gate \{show gate} \{show body})"

  show (Stop prf)
    = "Stop"

  show (Assign x y body)
    = "(Assign \{show x} \{show y} \{show body})"
  show (Mux out ctrl inA inB)
    = "(Mux \{show out} \{show ctrl} \{show inA} \{show inB})"
  show (GateU kind out inA)
    = "(GateU \{show kind} \{show out} \{show inA} )"

  show (GateB kind out inA inB)
    = "(GateB \{show kind} \{show out} \{show inA} \{show inB})"
  show (Split outA outB inp)
    = "(Collect \{show outA} \{show outB} \{show inp})"
  show (Collect out inA inB)
    = "(Collect \{show out} \{show inA} \{show inB})"

  show (Cast cast port)
    = "(Cast \{show cast} \{show port})"

  show (Index idir idx prf use prfT)
    = "(Index \{show idir} \{show idx} \{show (toNat prf)})"

  show (Project how prf use)
    = "(Project \{show how} \{show $ toNat prf})"
  show (ProjectAt how idx prf use prfT)
    = "(ProjectAt \{show how} \{show idx} \{show $ toNat prf})"

-- [ EOF ]
