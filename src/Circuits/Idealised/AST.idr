module Circuits.Idealised.AST

import Toolkit.Data.Location

import Ref
import Circuits.Types

%default total

public export
data End = F | L

public export
data AST = Var Ref
         | Input FileContext Direction DType Ref AST
         | Wire FileContext DType Ref Ref AST
         | Seq AST AST
         | Mux FileContext AST AST AST AST
         | Dup FileContext AST AST AST
         | Not FileContext AST AST
         | Gate FileContext AST AST AST
         | Stop FileContext
         | IndexS FileContext AST AST
         | IndexE FileContext End AST AST AST
         | IndexP FileContext Nat AST AST AST AST

-- [ EOF ]
