module Circuits.NetList.AST

import Toolkit.Data.Location
import Toolkit.Data.Whole

import Ref
import Circuits.NetList.Types

%default total

public export
data AST = Var Ref
         | Port FileContext Direction DType Ref AST
         | Wire FileContext DType Ref AST
         | GateDecl FileContext Ref AST AST

         | Mux FileContext AST AST AST AST

         | GateU FileContext Unary.Kind AST AST
         | GateB FileContext Binary.Kind AST AST AST

         | Index FileContext Whole AST
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

-- [ EOF ]
