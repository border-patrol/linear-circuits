||| Stuff that goes wrong.
|||
||| Module    : Error.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.Idealised.Error


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

import Circuits.Idealised.Lexer
import Circuits.Idealised.Types

%default total

namespace Check


  namespace FreeVar
    public export
    data LookupFail = NotFound String
                    | IsUsed String


  public export
  data FailingEdgeCase = InvalidSplit Nat Nat Nat Nat
                       | InvalidEdge  Nat Nat Nat

  public export
  data Error = Mismatch Ty Ty
             | ElemFail String (Exists.Error ())
             | PortExpected Direction
             | VectorExpected
             | VectorTooShort
             | VectorSizeMismatch Whole Whole Whole
             | LinearityError (Context (Ty,Usage) types)
             | Err FileContext Check.Error
             | NotEdgeCase FailingEdgeCase
             | MismatchGate DType DType


namespace Idealised

  public export
  data Error = TyCheck Check.Error
             | Parse   String (ParseError Token)
             | Sound   (Graph String) (HasExactDegree.Error String)


-- [ EOF ]
