module Circuits.Idealised.AST

import Toolkit.Data.Location

import Ref
import Circuits.Types

%default total

public export
data AST = Var Ref
         | Input FileContext Direction DType Ref AST
         | Wire FileContext DType Ref Ref AST
         | Seq AST AST
         | Dup FileContext AST AST AST
         | Not FileContext AST AST
         | Gate FileContext AST AST AST
         | Stop FileContext


-- [ EOF ]
