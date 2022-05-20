||| Stuff that goes wrong.
|||
||| Module    : Error.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Error

import Data.String
import Toolkit.Text.Parser.Run
import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Graph.EdgeBounded.HasExactDegree.All
import Toolkit.Data.Whole
import Toolkit.Data.Location
import Toolkit.Data.DList

import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.Common.Pretty
import Circuits.NetList.Lexer
import Circuits.NetList.Types

%default total

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


namespace Check
  public export
  data Error = Mismatch Ty Ty
             | MismatchD DType DType
             | NotBound String
             | VectorExpected
             | PortChanExpected
             | PortExpected
             | OOB Nat Nat
             | ErrI String
             | Err FileContext Check.Error


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


namespace NetList

  public export
  data Error = TyCheck Check.Error
             | Parse   String (ParseError Token)
             | Sound   (Graph String) (HasExactDegree.Error String)

  export
  Show (NetList.Error) where
    show (TyCheck x) = show x
    show (Parse f n) = show @{circuitspe} n
    show (Sound g e)
      = unlines ["// LOG : Soundness Error:", showErr (g, e)]


-- [ EOF ]
