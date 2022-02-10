module Circuits.Idealised.AST

import Toolkit.Data.Location

import Circuits.Idealised.Types

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
         | Gate FileContext GateKind AST AST AST
         | Stop FileContext
         | IndexS FileContext AST AST
         | IndexE FileContext End AST AST AST
         | IndexP FileContext Nat AST AST AST AST
         | MergeS FileContext AST AST
         | MergeV FileContext AST AST AST

export
setSource : String -> AST -> AST
setSource new (Var x)
  = Var ({span $= setSource new} x)

setSource new (Input x y z w v)
  = (Input (setSource new x)
           y
           z
           (setSource new w)
           (setSource new v))

setSource new (Wire x y z w v)
  = (Wire (setSource new x)
          y
          (setSource new z)
          (setSource new w)
          (setSource new v))

setSource new (Seq x y)
  = Seq (setSource new x)
        (setSource new y)

setSource new (Mux x y z w v)
  = (Mux (setSource new x)
         (setSource new y)
         (setSource new z)
         (setSource new w)
         (setSource new v))

setSource new (Dup x y z w)
  = (Dup (setSource new x)
         (setSource new y)
         (setSource new z)
         (setSource new w))

setSource new (Not x y z)
  = (Not (setSource new x)
         (setSource new y)
         (setSource new z))

setSource new (Gate x y z w v)
  = (Gate (setSource new x)
          y
          (setSource new z)
          (setSource new w)
          (setSource new v))

setSource new (Stop x)
  = (Stop (setSource new x))

setSource new (IndexS x y z)
  = (IndexS (setSource new x)
            (setSource new y)
            (setSource new z))

setSource new (IndexE x y z w v)
  = (IndexE (setSource new x)
            y
            (setSource new z)
            (setSource new w)
            (setSource new v))

setSource new (IndexP x k y z w v)
  = (IndexP (setSource new x)
            k
            (setSource new y)
            (setSource new z)
            (setSource new w)
            (setSource new v))

setSource new (MergeS fc o i)
  = MergeS (setSource new fc)
           (setSource new o)
           (setSource new i)

setSource new (MergeV fc o a b)
  = MergeV (setSource new fc)
           (setSource new o)
           (setSource new a)
           (setSource new b)

-- [ EOF ]
