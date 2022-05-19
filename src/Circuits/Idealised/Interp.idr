module Circuits.Idealised.Interp

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import public Toolkit.Decidable.Informative
import public Toolkit.Data.Graph.EdgeBounded
import public Toolkit.Data.Graph.EdgeBounded.HasExactDegree.All

import Toolkit.Data.Whole

import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.Idealised.Pretty

import Circuits.Idealised.Core

import Circuits.Idealised.Types
import Circuits.Idealised.Terms

%default total

public export
InterpTy : Ty -> Type
InterpTy TyUnit
  = Unit

InterpTy (TyPort x)
  = Vertex String

InterpTy TyGate
  = Graph String

namespace Environments
  public export
  data Env : List (Ty, Usage) -> Type where
    Empty  : Env Nil
    Extend : InterpTy type -> Env rest -> Env ((type,usage) :: rest)

  export
  lookup : (envO  : Env old )
        -> (prf   : IsVar old (type,FREE))
        -> (which : Use old prf new)
                  -> (Env new, InterpTy type)
  lookup {old = Nil} (Extend _ _) (V _ Here) H impossible

  lookup {old = ((type, FREE) :: rest)} (Extend x y) (V 0 Here) H
    = (Extend x y, x)
  lookup {old = ((type', usage') :: old)} (Extend a b) (V (S n) (There later)) (T x)
    = let (new, res) = lookup b (V n later) x
      in (Extend a new, res)

namespace Result

  public export
  data Result : (context : List (Ty, Usage))
             -> (type    : Ty)
                        -> Type
    where
      R : (counter : Nat)
       -> (env     : Env new)
       -> (graph   : Graph String)
       -> (result  : InterpTy type)
                  -> Result new type
  public export
  getResult : Result ctxt type -> InterpTy type
  getResult (R _ _ _ res) = res

  public export
  data GetGraph : (res : Result ctxt type) -> Graph String -> Type
    where
      G : (g : Graph String) -> GetGraph (R c e g r) g

  public export
  getGraph : (r : Result ctxt type) -> DPair (Graph String) (GetGraph r)
  getGraph (R counter env graph result) = MkDPair graph (G graph)


interp : (env     : Env old)
      -> (counter : Nat)
      -> (graph   : Graph String)
      -> (term    : Term old type new)
                 -> Result new type

-- [ NOTE ]
--
-- As normal
interp env counter graph (Var prf x)
  = let (newEnv, res) = lookup env prf x
    in R counter newEnv graph res

-- [ NOTE ]
--
-- As normal
interp env counter graph (Seq x y)
  = let R c1 e1 g1 x' = interp env counter graph x
    in interp e1 c1 ((merge g1 x')) y

-- [ NOTE ]
--
-- Ports are leaf nodes in the graph.
interp env counter graph (NewSignal flow dtype body)

  = let n = vertexFromFlow flow (S counter) 1

    in let env' = Extend n env

    in let g'   = insertNode n graph

    in interp env' (S counter) g' body

  where
    vertexFromFlow : Direction -> Nat -> Nat -> Vertex String
    vertexFromFlow INPUT  = driver  ("INPUT : "  <+> show dtype )
    vertexFromFlow OUTPUT = catcher ("OUTPUT : " <+> show dtype )

-- [ NOTE ]
--
-- Wires are internal connected nodes in the graph
interp env counter graph (Wire dtype body)

  = let c1 = S counter
    in let c2 = S c1

    in let chanIN  = node ("CHAN_IN : "  <+> show dtype) c1 1 1
    in let chanOUT = node ("CHAN_OUT : " <+> show dtype) c2 1 1

    in interp (Extend chanIN (Extend chanOUT env))
              c2
              (updateWith graph
                          [chanIN, chanOUT]
                          [(MkPair (ident chanIN) (ident chanOUT))])
              body


-- [ NOTE ]
--
-- Multiplexers are internal nodes connected to other nodes.
interp env counter graph (Mux o c l r)

  = let c1 = S counter

    in let mux = node "MUX" c1 3 1

    in let R c2 e1 g1 vo = interp env c1 graph  o
    in let R c3 e2 g2 vc = interp e1  c2 g1     c
    in let R c4 e3 g3 vl = interp e2  c2 g2     l
    in let R c5 e4 g4 vr = interp e3  c3 g3     r

    in let mg = fromLists [mux]
                          [ (ident vl,  ident mux)
                          , (ident vr,  ident mux)
                          , (ident vc,  ident mux)
                          , (ident mux, ident vo)
                          ]
    in R c5 e4 g4 mg

-- [ NOTE ]
--
-- Multiplexers are internal nodes connected to other nodes.
interp env counter graph (Dup a b i)
  = let c1 = S counter

    in let dup = node "DUP" c1 1 2

    in let R c2 e1 g1 va = interp env c1 graph a
    in let R c3 e2 g2 vb = interp e1  c2 g1    b
    in let R c4 e3 g3 vi = interp e2  c3 g2    i

    in let dg = fromLists [dup]
                          [ MkPair (ident vi)   (ident dup)
                          , MkPair (ident dup) (ident va)
                          , MkPair (ident dup) (ident vb)
                          ]

    in R c4 e3 g3 dg

-- [ NOTE ]
--
-- internal nodes connected to other nodes.
interp env counter graph (Not output input)
  = let c1 = S counter

    in let vnot = node "NOT" c1 1 1

    in let R c2 e1 g1 vo = interp env counter graph output
    in let R c3 e2 g2 vi = interp e1  c2      g1    input

    in let ng = fromLists [vnot]
                          [ MkPair (ident vnot) (ident vo)
                          , MkPair (ident vi)   (ident vnot)
                          ]
    in R c3 e2 g2 ng

-- [ NOTE ]
--
-- internal nodes connected to other nodes.
interp env counter graph (Gate k output inputA inputB)
   = let c1 = S counter

    in let bgate = node (show k) c1 2 1

    in let R c2 e1 g1 vo = interp env c1 graph output
    in let R c3 e2 g2 vl = interp e1  c2 g1    inputA
    in let R c4 e3 g3 vr = interp e2  c3 g2    inputB

    in let bg = fromLists [bgate]
                          [ MkPair (ident bgate) (ident vo)
                          , MkPair (ident vl) (ident bgate)
                          , MkPair (ident vr) (ident bgate)
                          ]

    in R c4 e3 g3 bg

-- [ NOTE ]
--
-- internal nodes connected to other nodes.
interp env counter graph (IndexSingleton o i)
  = let c1 = S counter

    in let vnot = node "IDX_SINGLETON" c1 1 1

    in let R c2 e1 g1 vo = interp env c1  graph o
    in let R c3 e2 g2 vi = interp e1  c2  g1    i

    in let ng = fromLists [vnot]
                          [ MkPair (ident vnot) (ident vo)
                          , MkPair (ident vi)   (ident vnot)
                          ]
    in R c3 e2 g2 ng


-- [ NOTE ]
--
-- internal nodes connected to other nodes.
interp env counter graph (IndexEdge p idx oused ofree i)

  = let c1 = S counter

    in let dup = node "IDX_EDGE" c1 1 2

    in let R c2 e1 g1 va = interp env c1 graph oused
    in let R c3 e2 g2 vb = interp e1  c2 g1    ofree
    in let R c4 e3 g3 vi = interp e2  c3 g2    i

    in let dg = fromLists [dup]
                          [ MkPair (ident vi)  (ident dup)
                          , MkPair (ident dup) (ident va)
                          , MkPair (ident dup) (ident vb)
                          ]

    in R c4 e3 g3 dg


-- [ NOTE ]
--
-- internal nodes connected to other nodes.
interp env counter graph (IndexSplit p idx used freeA freeB i)

  = let c1 = S counter

    in let dup = node "IDX_SPLIT" c1 1 3

    in let R c2 e1 g1 vu = interp env c1 graph used
    in let R c3 e2 g2 va = interp e1  c2 g1    freeA
    in let R c4 e3 g3 vb = interp e2  c3 g2    freeB
    in let R c5 e4 g4 vi = interp e3  c4 g3    i

    in let dg = fromLists [dup]
                          [ MkPair (ident vi)  (ident dup)
                          , MkPair (ident dup) (ident vu)
                          , MkPair (ident dup) (ident va)
                          , MkPair (ident dup) (ident vb)
                          ]

    in R c5 e4 g4 dg

-- [ NOTE ]
--
-- internal nodes connected to other nodes.
interp env counter graph (Merge2L2V output inputA inputB)

  = let c1 = S counter

    in let bgate = node "MERGE_2L2V" c1 2 1

    in let R c2 e1 g1 vo = interp env c1 graph output
    in let R c3 e2 g2 vl = interp e1  c2 g1    inputA
    in let R c4 e3 g3 vr = interp e2  c3 g2    inputB

    in let bg = fromLists [bgate]
                          [ MkPair (ident bgate) (ident vo)
                          , MkPair (ident vl) (ident bgate)
                          , MkPair (ident vr) (ident bgate)
                          ]

    in R c4 e3 g3 bg

-- [ NOTE ]
--
-- internal nodes connected to other nodes.
interp env counter graph (Merge2V2V prf output inputA inputB)

  = let c1 = S counter

    in let bgate = node "MERGE_2V2V" c1 2 1

    in let R c2 e1 g1 vo = interp env c1 graph output
    in let R c3 e2 g2 vl = interp e1  c2 g1    inputA
    in let R c4 e3 g3 vr = interp e2  c3 g2    inputB

    in let bg = fromLists [bgate]
                          [ MkPair (ident bgate) (ident vo)
                          , MkPair (ident vl) (ident bgate)
                          , MkPair (ident vr) (ident bgate)
                          ]

    in R c4 e3 g3 bg

-- [ NOTE ]
--
-- internal nodes connected to other nodes.
interp env counter graph (MergeSingleton output input)
  = let c1 = S counter

    in let vnot = node "MERGE_SINGLETON" c1 1 1

    in let R c2 e1 g1 vo = interp env counter graph output
    in let R c3 e2 g2 vi = interp e1  c2      g1    input

    in let ng = fromLists [vnot]
                          [ MkPair (ident vnot) (ident vo)
                          , MkPair (ident vi)   (ident vnot)
                          ]
    in R c3 e2 g2 ng

interp env counter graph (Stop x)
  = R counter Empty graph MkUnit


public export
data ValidGraph : Graph type -> Type where
  IsValid : HasExactDegrees vs es
         -> ValidGraph (MkGraph vs es)

export
validGraph : {type : Type}
          -> (g    : Graph type)
                  -> DecInfo (HasExactDegree.Error type)
                             (ValidGraph g)
validGraph (MkGraph nodes edges) with (hasExactDegrees nodes edges)
  validGraph (MkGraph nodes edges) | (Yes prf)
    = Yes (IsValid prf)
  validGraph (MkGraph nodes edges) | (No msg contra)
    = No msg (\(IsValid prf) => contra prf)


public export
data Valid : (res  : Result ctxt TyUnit)
                  -> Type
  where
    D : {res : Result ctxt TyUnit}
     -> (g   : Graph String)
            -> GetGraph res g
            -> ValidGraph g
            -> Valid res

isValid : (r : Result ctxt TyUnit)
            -> DecInfo (Graph String, HasExactDegree.Error String)
                       (Valid r)
isValid r with (getGraph r)
  isValid (R c e g r) | (MkDPair g (G g)) with (validGraph g)
    isValid (R c e g r) | (MkDPair g (G g)) | (Yes prf)
      = Yes (D g (G g) prf)
    isValid (R c e g r) | (MkDPair g (G g)) | (No msg contra)
      = No (g,msg) (\(D graph (G graph) prf) => contra prf)


public export
data IsSound : (term : Term Nil TyUnit Nil) -> Type where
  R : (prf  : Valid (interp Empty Z (MkGraph Nil Nil) term))
           -> IsSound term

public export
getGraph : IsSound term -> DPair (Graph String) ValidGraph
getGraph (R (D g x y)) = MkDPair g y

run : (term : Term Nil TyUnit Nil)
           -> DecInfo (Graph String, HasExactDegree.Error String) (IsSound term)
run term with (isValid (interp Empty Z empty term))
  run term | (Yes prf) = Yes (R prf)
  run term | (No msg contra) = No msg (\(R prf) => contra prf)


export
isSound : (term : Term Nil TyUnit Nil)
               -> Idealised (IsSound term)
isSound term
  = do prf <- embed (\(a,b) => Sound a b)
                    (run term)
       pure prf

-- [ EOF ]
