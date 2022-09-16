|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.AST

import Toolkit.Data.Location
import Toolkit.Data.Whole

import Circuits.NetList.Types

%default total

public export
data AST = Var Ref
         | Port FileContext Direction DType Ref AST
         | Wire FileContext DType Ref AST
         | GateDecl FileContext Ref AST AST

         | Shim FileContext Direction AST
         | Assign FileContext AST AST AST

         | Mux FileContext AST AST AST AST

         | GateU FileContext Unary.Kind AST AST
         | GateB FileContext Binary.Kind AST AST AST

         | Index FileContext Nat AST

         | Split   FileContext AST AST AST
         | Collect FileContext AST AST AST

         | Stop FileContext

export
setSource : String -> AST -> AST
setSource new (Var x)
  = Var ({span $= setSource new} x)

setSource new (Port x y z w v)
  = (Port (setSource new x)
           y
           z
           (setSource new w)
           (setSource new v))

setSource new (Wire x y z w)
  = (Wire (setSource new x)
          y
          (setSource new z)
          (setSource new w))

setSource new (GateDecl x v y z)
  = (GateDecl (setSource new x)
              (setSource new v)
          (setSource new y)
          (setSource new z))

setSource new (Assign fc i o rest)
  = Assign (setSource new fc)
           (setSource new i)
           (setSource new o)
           (setSource new rest)

setSource new (Shim fc d i)
  = Shim (setSource new fc)
         d
         (setSource new i)

setSource new (Mux x y z w v)
  = (Mux (setSource new x)
         (setSource new y)
         (setSource new z)
         (setSource new w)
         (setSource new v))

setSource new (GateU x k y z)
  = (GateU (setSource new x)
         k
         (setSource new y)
         (setSource new z))

setSource new (GateB x y z w v)
  = (GateB (setSource new x)
          y
          (setSource new z)
          (setSource new w)
          (setSource new v))

setSource new (Stop x)
  = (Stop (setSource new x))

setSource new (Index x y z)
  = (Index (setSource new x)
            y
            (setSource new z))

setSource new (Split fc a b i)
  = Split (setSource new fc)
          (setSource new a)
          (setSource new b)
          (setSource new i)

setSource new (Collect fc a b i)
  = Collect (setSource new fc)
            (setSource new a)
            (setSource new b)
            (setSource new i)



-- [ EOF ]
