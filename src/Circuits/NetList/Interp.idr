module Circuits.NetList.Interp

import Decidable.Equality

import Data.Nat
import Data.Fin
import Data.List.Elem
import Data.List.Quantifiers

import public Toolkit.Decidable.Informative
import public Toolkit.Data.Graph.EdgeBounded
import public Toolkit.Data.Graph.EdgeBounded.HasExactDegree.All

import Toolkit.Data.List.DeBruijn
import Toolkit.Data.Whole

import Circuits.NetList.Pretty
import Circuits.NetList.Types
import Circuits.NetList.Terms

%default total

public export
InterpTy : Ty -> Type
InterpTy TyUnit
  = Unit

InterpTy (TyPort x)
  = Vertex String

InterpTy (TyChan x)
  = (Vertex String, Vertex String)

InterpTy TyGate
  = Graph String

namespace Environments

  public export
  Env : List Ty -> Type
  Env = Env Ty InterpTy

namespace Result

  public export
  data Result : (type : Ty)
                     -> Type
    where
      R : (counter : Nat)
       -> (graph   : Graph String)
       -> (result  : InterpTy type)
                  -> Result type
  public export
  getResult : Result type -> InterpTy type
  getResult (R _ _ res) = res

  public export
  data GetGraph : (res : Result type) -> Graph String -> Type
    where
      G : (g : Graph String) -> GetGraph (R c g r) g

  public export
  getGraph : (r : Result type) -> DPair (Graph String) (GetGraph r)
  getGraph (R counter graph result) = MkDPair graph (G graph)

interp : (env     : Env ctxt)
      -> (counter : Nat)
      -> (graph   : Graph String)
      -> (term    : Term ctxt type)
                 -> Result type
interp env c g (Var x)
  = R c g (read x env)


-- [ NOTE ]
--
-- Ports are leaf nodes in the graph
interp env c g (Port flow dtype body)
    = let    c1 = S c
      in let v  = vertexFromFlow flow c1 (size dtype)

      in let R c2 g1 MkUnit = interp (extend env v)
                                     c1
                                     (insertNode v g)
                                     body
      in R c2 g1 MkUnit
  where
    vertexFromFlow : Direction -> Nat -> Nat -> Vertex String
    vertexFromFlow INPUT  = driver  ("INPUT : "  <+> show dtype )
    vertexFromFlow OUTPUT = catcher ("OUTPUT : " <+> show dtype )
    vertexFromFlow INOUT  = gateway ("INOUT : "  <+> show dtype )

-- [ NOTE ]
--
-- Wires are internal connected nodes in the graph
interp env c g (Wire dtype body)
    = let    c1      = S c
      in let c2      = S c1

      in let s = size dtype

      in let chanIN  = node ("CHAN_IN : "  <+> show dtype) c1 s 1
      in let chanOUT = node ("CHAN_OUT : " <+> show dtype) c2 1 s

      in let R c3 g2 MkUnit = interp (extend env (chanIN, chanOUT))
                                     c2
                                     (updateWith g [chanIN, chanOUT]
                                                   [MkPair (ident chanIN) (ident chanOUT)])
                                     body
      in R c3 g2 MkUnit

-- [ NOTES ]
--
--
interp env c g (GateDecl gate body)
  = let    R c1 g1 g2     = interp env c g gate
    in let R c2 g3 MkUnit = interp (extend env g2) c1 (merge g1 g2) body
    in     R c2 g3 MkUnit

-- [ NOTE ]
--
--
interp env c g Stop
  = R c g MkUnit

-- [ NOTE ]
--
-- 'Just' an edge
interp env c g (Assign {type} i o rest)
  = let    R c1 g1 vi = interp env c  g  i
    in let R c2 g2 vo = interp env c1 g1 o

    in let es = replicate (size type) (MkPair (ident vi) (ident vo))

    in interp env c2 (updateWith g2 Nil es)
                     rest

-- [ NOTE ]
--
-- Multiplexers are internal nodes connected to other nodes.
interp env c g (Mux o x l r)
    = let c1 = S c

      in let mux = node "MUX" c1 3 1

      in let R c2 g1 vo = interp env c1 g  o
      in let R c3 g2 vl = interp env c2 g1 l
      in let R c4 g3 vr = interp env c3 g2 r
      in let R c5 g4 vc = interp env c4 g3 x

      in R c5 g4
              (fromLists [mux] [ MkPair (ident vl)  (ident mux)
                               , MkPair (ident vr)  (ident mux)
                               , MkPair (ident vc)  (ident mux)
                               , MkPair (ident mux) (ident vo)
                               ])

-- [ NOTE ]
--
-- internal nodes connected to other nodes.
interp env c g (GateB x o l r)
    = let c1 = S c

      in let bgate = node (show x) c1 2 1

      in let R c2 g1 vo = interp env c1 g  o
      in let R c3 g2 vl = interp env c2 g1 l
      in let R c4 g3 vr = interp env c3 g2 r

      in R c4 g3
              (fromLists [bgate] [ MkPair (ident vl)    (ident bgate)
                                 , MkPair (ident vr)    (ident bgate)
                                 , MkPair (ident bgate) (ident vo)
                                 ])

-- [ NOTE ]
--
-- Multiplexers are internal nodes connected to other nodes.
interp env c g (GateU x o i)
    = let c1 = S c

      in let ugate = node (show x) c1 1 1

      in let R c2 g1 vo = interp env c1 g  o
      in let R c3 g2 vi = interp env c2 g1 i

      in R c3 g2
              (fromLists [ugate] [ MkPair (ident vi)    (ident ugate)
                                 , MkPair (ident ugate) (ident vo)
                                 ])

-- [ NOTE ]
--
-- Indexing ports creates a new edge in the graph to a node representing the index.
--
interp env c g (Index dir what idx)
    = let c1 = S c

      in let idxVertex = both ("IDX [" <+> show (finToNat idx) <+> "](" <+>  show dir <+>")" ) c1 1

      in let R c2 gsub whatVertex = interp env c1 g what

      in R c2 (updateWith gsub [idxVertex]
                               (buildEdge dir whatVertex idxVertex))
              idxVertex
  where buildEdge : Index direc -> (a,b : Vertex String) -> Edges
        buildEdge (UP x)   a b = [MkPair (ident b) (ident a)]
        buildEdge (DOWN x) a b = [MkPair (ident a) (ident b)]

-- [ NOTE ]
--
-- Projection of channels returns the channel's appropriate endpoint.
interp env c g (Project how chan)

    = let R c1 g2 (i,o) = interp env c g chan


      in R c1 g2
              (selectNode how i o)

  where selectNode : Project dir -> Vertex String -> Vertex String -> Vertex String
        selectNode WRITE i _ = i
        selectNode READ  _ o = o

-- [ NOTE]
--
-- Splitting inserts a node.
interp env c g (Split a b i)

  = let c1 = S c
    in let s = size LOGIC

    in let sVertex = both "SPLIT" c1 s

    in let R c2 g1 av = interp env c1 g  a
    in let R c3 g2 bv = interp env c2 g1 b
    in let R c4 g3 iv = interp env c3 g2 i

    in let esIS = replicate s (MkPair (ident iv)      (ident sVertex))
    in let esSA = replicate s (MkPair (ident sVertex) (ident av))
    in let esSB = replicate s (MkPair (ident sVertex) (ident bv))

    in R c4 g3
            (fromLists [av,bv,iv,sVertex]
                       (esIS ++ esSA ++ esSB))

interp env c g (Collect {type} o a b)

  = let c1 = S c
    in let s = size type

    in let sVertex = both "COLLECT" c1 s

    in let R c2 g1 ov = interp env c1 g  o
    in let R c3 g2 av = interp env c2 g1 a
    in let R c4 g3 bv = interp env c3 g2 b

    in let esAC = replicate s (MkPair (ident av) (ident sVertex))
    in let esBC = replicate s (MkPair (ident bv) (ident sVertex))
    in let esSO = replicate s (MkPair (ident sVertex) (ident ov))

    in R c4 g3
            (fromLists [ov,av,bv,sVertex]
                       (esAC ++ esBC ++ esSO))


-- [ NOTE ]
--
-- Casting inserts a new edge
interp env c g (Cast {type} how what)
    = let c1 = S c

      in let s = size type

      in let cVertex = both "CAST" c1 s

      in let R c2 g1 what = interp env c1 g what

      in let es = replicate s (buildEdge how cVertex what)

      in R c2 (updateWith g1 [cVertex] es)
              cVertex

  where buildEdge : Cast INOUT r -> (a,b : Vertex String) -> Edge
        buildEdge BI a b = MkPair (ident b) (ident a)
        buildEdge BO a b = MkPair (ident a) (ident b)



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
data Valid : (res  : Result TyUnit)
                  -> Type
  where
    D : {res : Result TyUnit}
     -> (g   : Graph String)
            -> GetGraph res g
            -> ValidGraph g
            -> Valid res

isValid : (r : Result TyUnit)
            -> DecInfo (Graph String, HasExactDegree.Error String)
                       (Valid r)
isValid r with (getGraph r)
  isValid (R c g r) | (MkDPair g (G g)) with (validGraph g)
    isValid (R c g r) | (MkDPair g (G g)) | (Yes prf)
      = Yes (D g (G g) prf)
    isValid (R c g r) | (MkDPair g (G g)) | (No msg contra)
      = No (g,msg) (\(D graph (G graph) prf) => contra prf)

public export
data Run : (term : Term Nil TyUnit) -> Type where
  R : (prf  : Valid (interp Nil Z (MkGraph Nil Nil) term))
           -> Run term

public export
getGraph : Run term -> DPair (Graph String) ValidGraph
getGraph (R (D g x y)) = MkDPair g y

export
run : (term : Term Nil TyUnit)
           -> DecInfo (Graph String, HasExactDegree.Error String) (Run term)
run term with (isValid (interp Nil Z empty term))
  run term | (Yes prf) = Yes (R prf)
  run term | (No msg contra) = No msg (\(R prf) => contra prf)

export
runIO : (term : Term Nil TyUnit)
             -> IO (Either (Graph String, HasExactDegree.Error String)
                           (Run term))
runIO term = pure $ (asEither (run term))

-- [ EOF ]
