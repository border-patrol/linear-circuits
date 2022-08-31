||| Stuff that goes wrong.
|||
||| Module    : Error.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Error

import Data.String

import Toolkit.Data.Location
import Toolkit.Text.Parser.Run
import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Graph.EdgeBounded.HasExactDegree.All
import Toolkit.Data.DList

import public Toolkit.DeBruijn.Context.Item
import public Toolkit.DeBruijn.Context

import Circuits.Common.Pretty

import        Circuits.NetList.Lexer
import public Circuits.NetList.Types

import Circuits.NetList.Linear.Usage

%default total

namespace NetList
  namespace Linear
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
                 | LinearityError (List String)



    public export
    data Error = TyCheck Check.Error
               | Parse   String (ParseError Token)
               | Sound   (Graph String) (HasExactDegree.Error String)


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

  show (LinearityError names)
    = "Linearity Error:\n\{unlines names}"

export
Show (NetList.Linear.Error) where
  show (TyCheck x) = show x
  show (Parse f n) = show @{circuitspe} n
  show (Sound g e)
    = unlines ["// LOG : Soundness Error:", showErr (g, e)]

-- [ EOF ]
