|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Interp

import Decidable.Equality

import Data.Nat
import Data.Fin
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Decidable.Informative

import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Graph.EdgeBounded.HasExactDegree.All

import Toolkit.Data.DList
import Toolkit.Data.Whole

import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming
import Toolkit.DeBruijn.Environment


import Circuits.NetList.Types

import Circuits.NetList.Linear.Core
import Circuits.NetList.Linear.Usage
import Circuits.NetList.Linear.Terms

import Circuits.NetList.Linear.Pretty

%default total

public export
InterpTy : Ty -> Type
InterpTy TyUnit
  = Unit

InterpTy (TyPort x)
  = Vertex String

InterpTy (TyChan x)
  = Pair (Vertex String) (Vertex String)

InterpTy TyGate
  = Graph String


select : Project dir -> Vertex a -> Vertex a -> Vertex a
select WRITE y z = y
select READ y z = z


namespace Linear

  public export
  data Erase : Item -> Ty -> Type where
    E : Erase (I t u) t

  public export
  data Value : Item -> Type where
    V : Erase i t -> InterpTy t -> Value i

  public export
  Env : List Item -> Type
  Env = Env Item Value

  namespace Port

    use : Value (I t u)
       -> Port.Use (I t u) pF u' pU
       -> Pair (Value u') (InterpTy t)
    use (V E z) (U prf)
      = MkPair (V E z) z

    export
    lookup : {that : List Item}
          -> (env : Env this)
          -> (prf : IsFreePort (I (TyPort (flow,type)) u) this)
          -> (use : UsePort this prf that)
                 -> (Env that, InterpTy (TyPort (flow,type)))
    lookup (v :: vs) (Here Refl prfSat) (UpdateHere uprf)
      = let (v',p) = use v uprf in (v' :: vs, p)
    lookup (v :: vs) (There rest) (UpdateThere x) with (lookup vs rest x)
      lookup (v :: vs) (There rest) (UpdateThere x) | (env, z)
        = (v :: env, z)

  namespace Chan

    export
    lookup : (env : Env this)
          -> (prf : Elem IsChan (I (TyChan t) (TyChan i o)) this)
                 -> InterpTy (TyChan t)
    lookup ((V E y) :: rest) (Here Refl (IC x))
      = y
    lookup (elem :: x) (There rest)
      = lookup x rest

  namespace Gate

    export
    lookup : (env : Env this)
          -> (prf : Elem IsGate (I TyGate TyGate) this)
                 -> InterpTy TyGate
    lookup ((V E y) :: rest) (Here Refl IG)
      = y
    lookup (elem :: x) (There rest)
      = lookup x rest

  namespace Proj

    use : Value (I t u)
       -> Use how (I t u) pF u' pU
       -> Pair (Value u') (InterpTy t)
    use (V E z) (U prf)
      = MkPair (V E z) z

    export
    lookup : {that : List Item}
          -> (env : Env this)
          -> (prf : CanProject how (I (TyChan type) u) this)
          -> (use : UseChannel how this prf that)
                 -> (Env that, InterpTy (TyChan type))
    lookup (v :: vs) (Here Refl prfSat) (UpdateHere uprf)
      = let (v',c) = use v uprf in (v'::vs, c)

    lookup (v::vs) (There rest) (UpdateThere x) with (lookup vs rest x)
      lookup (v::vs) (There rest) (UpdateThere x) | (env, z)
        = (v :: env, z)

    namespace Index

      use : Value (I t u)
         -> UseAt how idx (I t u) pF u' pU
         -> Pair (Value u') (InterpTy t)
      use (V E z) (UAt prf)
        = MkPair (V E z) z

      export
      lookup : {that : List Item}
            -> (env : Env this)
            -> (prf : CanProjectAt how
                                   idx
                                   (I (TyChan (BVECT (W (S n) ItIsSucc) type))
                                   u)
                                   this)
            -> (use  : UseChannelAt how idx this prf that)

                   -> (Env that, InterpTy ((TyChan (BVECT (W (S n) ItIsSucc) type))))
      lookup (v::vs) (Here Refl prfSat) (UpdateHere uprf)
        = let (v',p) = use v uprf in (v'::vs,p)

      lookup (v::vs) (There rest) (UpdateThere x) with (lookup vs rest x)
        lookup (v::vs) (There rest) (UpdateThere x) | (env, z)
          = (v :: env, z)

  namespace Index

    use : Value (I t u)
       -> UseAt idx (I t u) pF u' pU
       -> Pair (Value u') (InterpTy t)
    use (V E z) (UAt prf)
      = MkPair (V E z) z

    export
    lookup : {that : List Item}
          -> (env : Env this)
          -> (prf : IsFreePortAt idx
                                 (I (TyPort (flow, BVECT (W (S n) ItIsSucc) type))
                                 u)
                                 this)
          -> (use  : UsePortAt idx this prf that)

                 -> (Env that, InterpTy ((TyPort (flow, BVECT (W (S n) ItIsSucc) type))))
    lookup (v::vs) (Here Refl prfSat) (UpdateHere uprf)
      = let (v',p) = use v uprf in (v'::vs,p)

    lookup (v::vs) (There rest) (UpdateThere x) with (lookup vs rest x)
      lookup (v::vs) (There rest) (UpdateThere x) | (env, z)
        = (v :: env, z)

namespace Result

  public export
  data Result : (context : List Item)
             -> (type    : Ty)
                        -> Type
   where
     R : (counter : Nat)
      -> (env     : Env      new)
      -> (graph   : Graph String)
      -> (result  : InterpTy     type)
                 -> Result   new type

  public export
  getResult : Result ctxt type -> InterpTy type
  getResult (R counter env g result) = result

  public export
  data GetGraph : (res : Result.Result ctxt type) -> Graph String -> Type
    where
      G : (g : Graph String) -> GetGraph (R c e g r) g

  public export
  getGraph : (r : Result.Result ctxt type) -> DPair (Graph String) (GetGraph r)
  getGraph (R counter env graph result) = MkDPair graph (G graph)


interp : (counter : Nat)
      -> (env     : Env this)
      -> (graph   : Graph String)
      -> (term    : Term this type that)
                 -> Result that type

-- ## Lookups

interp c e g (FreePort prf use)
  = let (new, p) = lookup e prf use
    in R c new g p

interp c e g (VarGate prf)
  = let g' = lookup e prf
    in R c e g g'

interp c e g (VarChan prf)
  = let c' = lookup e prf
    in R c e g c'

-- ## Binders

-- ### Ports
--
-- Ports are leaf nodes in the graph, need to make sure they are the
-- right sort...
interp c e g (Port flow dtype (I y) body)
  =  let c1 = S c

  in let v = vertexFromFlow flow c1 (size dtype)

  in let R c2 e1 g1 MkUnit = interp c1
                                    (V E v :: e)
                                    (insertNode v g)
                                    body
  in R c2 e1 g1 MkUnit

  where
    vertexFromFlow : Direction -> Nat -> Nat -> Vertex String
    vertexFromFlow INPUT  = driver  ("INPUT : \{show dtype}")
    vertexFromFlow OUTPUT = catcher ("OUTPUT : \{show dtype}")
    vertexFromFlow INOUT  = gateway ("INOUT : \{show dtype}")

-- ### Wires
--
-- Wires are channels with endpoints.
--
-- + Each endpoint inputs/outputs |dtype| wires.
-- + There is a single connection between endpoints.
interp c e g (Wire dtype (I x) body)
  =  let c1 = S c
  in let c2 = S c1

  in let s = size dtype

  in let chanI = node ("CHAN_IN : \{show dtype}")  c1 s 1
  in let chanO = node ("CHAN_OUT : \{show dtype}") c2 1 s

  in let R c3 e1 g2 MkUnit = interp c2
                                    (V E (chanI,chanO)::e)
                                    (updateWith g [chanI,chanO]
                                                  [MkPair (ident chanI) (ident chanO)])
                                    body
  in R c3 e1 g2 MkUnit

-- ### Gates
--
-- Gates generate a graph that needs merging in.
interp c e g (Gate gate body)
  = let R c1 e1 g1 gate = interp c e g gate
    in interp c1
              (V E gate::e1)
              (merge g1 gate)
              body

-- ## Stopping
--
-- Return nothing.
interp c e g (Stop prf)
  = R c Nil g MkUnit

-- ## Assignments
--
-- Just an edge, one for each wire, between ports.
interp c e g (Assign {type} o i body)

  = let    R c1 e1 g1 o = interp c  e  g  o
    in let R c2 e2 g2 i = interp c1 e1 g1 i

    in let es = List.replicate (size type) (MkPair (ident i) (ident o))

    in interp c2 e2 (updateWith g2 Nil es)
                    body

-- ## Gates

-- They are all internal nodes presented as individual graphs.
{-
interp e c g (Mux o s l r)

-}

interp c e g (Mux o s l r)
  =  let c1 = S c

  in let mux = node "MUX" c1 3 1

  in let R c2 e1 g1 vo = interp c1 e  g  o
  in let R c3 e2 g2 vc = interp c2 e1 g1 s
  in let R c4 e3 g3 vl = interp c2 e2 g2 l
  in let R c5 e4 g4 vr = interp c3 e3 g3 r

  in let mg = fromLists [mux]
                        [ (ident vl,  ident mux)
                        , (ident vr,  ident mux)
                        , (ident vc,  ident mux)
                        , (ident mux, ident vo)
                        ]
  in R c5 e4 g4 mg

-- ### Unary Logic Gates
--
-- Create an internal node with one output and one input.
--
-- Connect all the wires together.
--
interp c e g (GateU kind o i)
  =  let c1 = S c

  in let ugate = node (show kind) c1 1 1

  in let R c2 e1 g1 vo = interp c1 e  g  o
  in let R c3 e2 g2 vi = interp c2 e1 g1 i

  in R c3 e2 g2
          (fromLists [ugate] [ MkPair (ident vi)    (ident ugate)
                             , MkPair (ident ugate) (ident vo)
                             ])

-- ### Binary Logic Gates
--
-- Create an internal node with one output and two inputs.
--
-- Connect all the wires together.
--
interp c e g (GateB kind out inA inB)
   =  let c1 = S c

   in let bgate = node (show kind) c1 2 1

   in let R c2 e1 g1 vo = interp c1 e  g  out
   in let R c3 e2 g2 vl = interp c2 e1 g1 inA
   in let R c4 e3 g3 vr = interp c3 e2 g2 inB

   in let bg = fromLists [bgate]
                         [ MkPair (ident bgate) (ident vo)
                         , MkPair (ident vl)   (ident bgate)
                         , MkPair (ident vr)   (ident bgate)
                         ]

   in R c4 e3 g3 bg

-- ### Splitting Wires
--
-- Duplicate a single wires.
--
-- Connect all the wires together.
--
interp c e g (Split outA outB inp)
  =  let c1 = S c
  in let s = size LOGIC

  in let sVertex = both "SPLIT" c1 s

  in let R c2 e1 g1 av = interp c1 e  g  outA
  in let R c3 e2 g2 bv = interp c2 e1 g1 outB
  in let R c4 e3 g3 iv = interp c3 e2 g2 inp

  in let esIS = replicate s (MkPair (ident iv)      (ident sVertex))
  in let esSA = replicate s (MkPair (ident sVertex) (ident av))
  in let esSB = replicate s (MkPair (ident sVertex) (ident bv))

  in R c4 e3
          g3
          (fromLists [av,bv,iv,sVertex]
                     (esIS ++ esSA ++ esSB))

-- ### Collecting Wires
--
-- Create an internal node |type| inputs and outputs.
--
-- Connect all the wires together.
--
interp c e g (Collect {type} out inA inB)
  =  let c1 = S c

  in let s = size type

  in let sVertex = both "COLLECT" c1 s

  in let R c2 e1 g1 ov = interp c1 e  g  out
  in let R c3 e2 g2 av = interp c2 e1 g1 inA
  in let R c4 e3 g3 bv = interp c3 e2 g2 inB

  in let esAC = replicate s (MkPair (ident av)      (ident sVertex))
  in let esBC = replicate s (MkPair (ident bv)      (ident sVertex))
  in let esSO = replicate s (MkPair (ident sVertex) (ident ov))

  in R c4 e3
          g3
          (fromLists [ov,av,bv,sVertex]
                     (esAC ++ esBC ++ esSO))

-- ## Casting
--
-- They are 'just' internal gates that act as a valve for direction flow.
--
-- Need to make sure they go in the write direction.
--
interp c e g (Cast cast port)
    =  let c1 = S c

    in let cVertex = both "CAST" c1 1

    in let R c2 e1 g1 what = interp c1 e g port

    in R c2 e1
            (updateWith g1 [cVertex] [buildEdge cast cVertex what])
            cVertex

  where buildEdge : Cast INOUT r -> (a,b : Vertex String) -> Edge
        buildEdge BI a b = MkPair (ident b) (ident a)
        buildEdge BO a b = MkPair (ident a) (ident b)

-- ## Indexing & Projections

-- ### Indexing
--
-- Indexing creates a node for the index that has |typeo| ports, where
-- typeo is the size of the element at the end of the index.
--
interp c e g (Index {typeo} idir idx prf use prfT)
  =  let c1 = S c

--  in let s = size typeo
--
--  in let idxVertex = both ("IDX [\{show idx}](\{show idir})") c1 s

  in let (new,p) = lookup e prf use

--  in let es = replicate s (buildEdge idir p idxVertex)

  in R c1 new
       g -- (updateWith g [idxVertex] es)
       p -- idxVertex

  where buildEdge : Index flow -> (a,b : Vertex String) -> Edge
        buildEdge (UP x)   a b = MkPair (ident b) (ident a)
        buildEdge (DOWN x) a b = MkPair (ident a) (ident b)

-- ### Projections
-- #### Simple
--
-- Projection just chooses the correct end of the channel.
interp c e g (Project how prf use)

  = let (new, (i,o)) = lookup e prf use
    in R c new g (selectNode how i o)

  where selectNode : Project dir -> Vertex String -> Vertex String -> Vertex String
        selectNode WRITE i _ = i
        selectNode READ  _ o = o

-- #### Indexed
interp c e g (ProjectAt {typeo} how idx prf use prfT)
  =  let c1 = S c

  in let s = size typeo

  in let idxVertex = both ("IDXProj [\{show idx}](\{show how})") c1 s

  in let (new,(i,o)) = Proj.Index.lookup e prf use

  in let es = replicate s (buildEdge how i o idxVertex)

  in R c1 new (updateWith g [idxVertex] es) idxVertex

  where buildEdge : Project dir -> (i,o,a : Vertex String)-> Edge
        buildEdge WRITE i _ a = MkPair (ident a) (ident i)
        buildEdge READ  _ o a = MkPair (ident o) (ident a)

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
  R : (prf  : Valid (interp Z Nil (MkGraph Nil Nil) term))
           -> IsSound term

public export
getGraph : IsSound term -> DPair (Graph String) ValidGraph
getGraph (R (D g x y))
  = MkDPair g y


run : (term : Term Nil TyUnit Nil)
           -> DecInfo (Graph String, HasExactDegree.Error String)
                      (IsSound term)
run term with (isValid (interp Z Nil empty term))
  run term | (Yes prf)
    = Yes (R prf)
  run term | (No msg contra)
    = No msg (\(R prf) => contra prf)

export
isSound : (term : Term Nil TyUnit Nil)
               -> Linear (IsSound term)

isSound term
  = embed (\(a,b) => Sound a b)
          (run term)

-- [ EOF ]
