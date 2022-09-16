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

import Toolkit.Data.Whole
import Toolkit.Data.List.DeBruijn

import Circuits.NetList.Types

import Circuits.NetList.Linear.Usage
import Circuits.NetList.Linear.Terms

import Circuits.NetList.Pretty

%default total
{-
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

namespace Environments

  public export
  data Env : List Item -> Type where
    Empty  : Env Nil
    Extend : (term : InterpTy type)
          -> (env  : Env rest)
                  -> Env (I type usage :: rest)


  namespace Port

    export
    lookup : (env : Env this)
          -> (prf : IsFreePort (I (TyPort (flow,type)) u) this)
          -> (use : UsePort this prf that)
                 -> (Env that, InterpTy (TyPort (flow,type)))
    lookup (Extend term rest) (FreePortHere pf) (UsePortHere use)
      = (Extend term rest, term)

    lookup (Extend not_term env) (FreePortThere rest) (UsePortThere later) with (lookup env rest later)
      lookup (Extend not_term env) (FreePortThere rest) (UsePortThere later) | (new, term)
        = (Extend not_term new, term)

  namespace Project

    export
    lookup : (env : Env this)
          -> (prf : IsFreeChannel how (I (TyChan type) (TyChan ein eout)) this)
          -> (use : ProjectChannel how this prf that)
                 -> (Env that, InterpTy (TyChan type))
    lookup (Extend term env) (FreeChannelHere prf) (ProjectHere use)
      = (Extend term env, term)

    lookup (Extend not_term env) (FreeChannelThere rest) (ProjectThere later) with (lookup env rest later)
      lookup (Extend not_term env) (FreeChannelThere rest) (ProjectThere later) | (new, term)
        = (Extend not_term new, term)

  namespace Index

   export
   lookup : (env : Env this)
         -> (prf : CanIndexPort idx (I (TyPort (flow, BVECT (W (S n) ItIsSucc) type)) u) this)
         -> (use : IndexPort idx this prf that)
                -> (Env that, InterpTy (TyPort (flow, type)))
   lookup (Extend term env) (CanIndexHere prf) (IndexHere use)
     = (Extend term env, term)

   lookup (Extend not_term env) (CanIndexThere rest) (IndexThere later) with (lookup env rest later)
     lookup (Extend not_term env) (CanIndexThere rest) (IndexThere later) | (new, term)
       = (Extend not_term new, term)

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


interp : (env     : Env this)
      -> (counter : Nat)
      -> (graph   : Graph String)
      -> (term    : Term this type that)
                 -> Result that type

-- [ NOTE ]
--
-- As normal
interp e c g (VarPort prf use)

  = let (new, ret) = lookup e prf use
    in R c new g ret

-- [ NOTE ]
--
-- Ports are leaf nodes in the graph.
interp e c g (Port flow dtype (FP u prf) body)
    = let    c1 = S c
      in let v  = vertexFromFlow flow c1 (size dtype)

      in let R e1 c2 g1 MkUnit = interp (Extend v e)
                                        c1
                                        (insertNode v g)
                                        body
      in R e1 c2 g1 MkUnit

  where
    vertexFromFlow : Direction -> Nat -> Nat -> Vertex String
    vertexFromFlow INPUT  = driver  ("INPUT : "  <+> show dtype )
    vertexFromFlow OUTPUT = catcher ("OUTPUT : " <+> show dtype )
    vertexFromFlow INOUT  = gateway ("INOUT : "  <+> show dtype )


interp e c g (Wire dtype (FC u prf) body)
  = let    c1 = S c
    in let c2 = S c1

    in let s = size dtype

    in let chanIN  = node ("CHAN_IN : "  <+> show dtype) c1 s 1
    in let chanOUT = node ("CHAN_OUT : " <+> show dtype) c2 1 s

    in let R e1 c3 g2 MkUnit = interp (Extend (chanIN, chanOUT) e)
                                      c2
                                      (updateWith g [chanIN, chanOUT]
                                                    [MkPair (ident chanIN) (ident chanOUT)])
                                       body
    in R e1 c3 g2 MkUnit


interp e c g (Gate gate body)
  = let R c1 e1 g1 res = interp e c g gate
    in interp (Extend res e1) c1 (merge g res) body

interp e c g (Stop prf)
  = R c Empty g MkUnit


interp e c g (Mux o s l r)

  = let c1 = S c

    in let mux = node "MUX" c1 3 1

    in let R c2 e1 g1 vo = interp e  c1 g  o
    in let R c3 e2 g2 vc = interp e1 c2 g1 s
    in let R c4 e3 g3 vl = interp e2 c2 g2 l
    in let R c5 e4 g4 vr = interp e3 c3 g3 r

    in let mg = fromLists [mux]
                          [ (ident vl,  ident mux)
                          , (ident vr,  ident mux)
                          , (ident vc,  ident mux)
                          , (ident mux, ident vo)
                          ]
    in R c5 e4 g4 mg

interp e c g (GateU kind o i)
    = let c1 = S c

      in let ugate = node (show kind) c1 1 1

      in let R c2 e1 g1 vo = interp e  c1 g  o
      in let R c3 e2 g2 vi = interp e1 c2 g1 i

      in R c3 e2 g2
              (fromLists [ugate] [ MkPair (ident vi)    (ident ugate)
                                 , MkPair (ident ugate) (ident vo)
                                 ])

interp e c g (GateB kind o l r)

   = let c1 = S c

    in let bgate = node (show kind) c1 2 1

    in let R c2 e1 g1 vo = interp e  c1 g  o
    in let R c3 e2 g2 vl = interp e1 c2 g1 l
    in let R c4 e3 g3 vr = interp e2 c3 g2 r

    in let bg = fromLists [bgate]
                          [ MkPair (ident bgate) (ident vo)
                          , MkPair (ident vl) (ident bgate)
                          , MkPair (ident vr) (ident bgate)
                          ]

    in R c4 e3 g3 bg

interp e c g (Split a b i)

  = let c1 = S c
    in let s = size LOGIC

    in let sVertex = both "SPLIT" c1 s

    in let R c2 e1 g1 av = interp e  c1 g  a
    in let R c3 e2 g2 bv = interp e1 c2 g1 b
    in let R c4 e3 g3 iv = interp e2 c3 g2 i

    in let esIS = replicate s (MkPair (ident iv)      (ident sVertex))
    in let esSA = replicate s (MkPair (ident sVertex) (ident av))
    in let esSB = replicate s (MkPair (ident sVertex) (ident bv))

    in R c4 e3
            g3
            (fromLists [av,bv,iv,sVertex]
                       (esIS ++ esSA ++ esSB))

interp e c g (Collect {type} o a b)

  = let c1 = S c
    in let s = size type

    in let sVertex = both "COLLECT" c1 s

    in let R c2 e1 g1 ov = interp e  c1 g  o
    in let R c3 e2 g2 av = interp e1 c2 g1 a
    in let R c4 e3 g3 bv = interp e2 c3 g2 b

    in let esAC = replicate s (MkPair (ident av) (ident sVertex))
    in let esBC = replicate s (MkPair (ident bv) (ident sVertex))
    in let esSO = replicate s (MkPair (ident sVertex) (ident ov))

    in R c4 e3
            g3
            (fromLists [ov,av,bv,sVertex]
                       (esAC ++ esBC ++ esSO))

interp e c g (Cast cast port)
    = let c1 = S c

      in let cVertex = both "CAST" c1 1

      in let R c2 e1 g1 what = interp e c1 g port

      in R c2 e1
              (updateWith g1 [cVertex] [buildEdge cast cVertex what])
              cVertex

  where buildEdge : Cast INOUT r -> (a,b : Vertex String) -> Edge
        buildEdge BI a b = MkPair (ident b) (ident a)
        buildEdge BO a b = MkPair (ident a) (ident b)


interp e c g (Project how prf use)

    = let (new, (i,o)) = lookup e prf use

      in R c new g (selectNode how i o)

  where selectNode : Project dir -> Vertex String -> Vertex String -> Vertex String
        selectNode WRITE i _ = i
        selectNode READ  _ o = o

interp e c g (Index dir idx prf use)
    = let c1 = S c

      in let idxVertex = both ("IDX [" <+> show (finToNat idx) <+> "](" <+>  show dir <+>")" ) c1 1

      in let (new,p) = lookup e prf use

      in R c1 new (updateWith g [idxVertex]
                               (buildEdge dir p idxVertex))
              idxVertex
  where buildEdge : Index direc -> (a,b : Vertex String) -> Edges
        buildEdge (UP x)   a b = [MkPair (ident b) (ident a)]
        buildEdge (DOWN x) a b = [MkPair (ident a) (ident b)]

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
data Run : (term : Term Nil TyUnit Nil) -> Type where
  R : (prf  : Valid (interp Empty Z (MkGraph Nil Nil) term))
           -> Run term

public export
getGraph : Run term -> DPair (Graph String) ValidGraph
getGraph (R (D g x y)) = MkDPair g y

export
run : (term : Term Nil TyUnit Nil)
           -> DecInfo (Graph String, HasExactDegree.Error String) (Run term)
run term with (isValid (interp Empty Z empty term))
  run term | (Yes prf) = Yes (R prf)
  run term | (No msg contra) = No msg (\(R prf) => contra prf)

export
runIO : (term : Term Nil TyUnit Nil)
             -> IO (Either (Graph String, HasExactDegree.Error String)
                           (Run term))
runIO term = pure $ (asEither (run term))
-}
-- [ EOF ]
