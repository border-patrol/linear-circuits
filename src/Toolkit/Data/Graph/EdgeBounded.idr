||| A graph whose vertices have a restricted in/out degree.
module Toolkit.Data.Graph.EdgeBounded

import Decidable.Equality

import Data.String
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Decidable.Do

import Toolkit.Data.Nat
import Toolkit.Data.Pair
import Toolkit.Data.List.Size
import Toolkit.Data.List.Occurs

%default total

namespace Vertex
  public export
  data Flow = SRC | SNK | BI

  export
  Show Flow where
    show SRC = "IN"
    show SNK = "OUT"
    show BI = "INOUT"

  Uninhabited (SRC = SNK) where
    uninhabited Refl impossible

  Uninhabited (SRC = BI) where
    uninhabited Refl impossible

  Uninhabited (SNK = BI) where
    uninhabited Refl impossible

  DecEq Flow where
    decEq SRC SRC = Yes Refl
    decEq SRC SNK = No absurd
    decEq SRC BI = No absurd
    decEq SNK SRC = No (negEqSym absurd)
    decEq SNK SNK = Yes Refl
    decEq SNK BI = No absurd
    decEq BI SRC = No (negEqSym absurd)
    decEq BI SNK = No (negEqSym absurd)
    decEq BI BI = Yes Refl


  public export
  data Vertex = Node Nat Nat Nat
              | Leaf Flow Nat Nat

  export
  Show Vertex where
    show (Node k j i) = show k <+> " [label=\"" <+> show (j,i) <+> "\"];"
    show (Leaf x k j) = show k <+> " [label=\"" <+> withFlow x j <+> "\"];"
      where withFlow : Flow -> Nat -> String
            withFlow f k = show f <+> "(" <+> show k <+>")"

  Uninhabited (Node k j i = Leaf s x y) where
    uninhabited Refl impossible

  decEq : (a,b : Vertex) -> Dec (a = b)
  decEq (Node k j i) (Node a b c)
    = decDo $ do Refl <- decEq k a `otherwise` (\Refl => Refl)
                 Refl <- decEq j b `otherwise` (\Refl => Refl)
                 Refl <- decEq i c `otherwise` (\Refl => Refl)
                 pure Refl

  decEq (Node _ _ _) (Leaf _ _ _) = No absurd

  decEq (Leaf _ _ _) (Node _ _ _) = No (negEqSym absurd)

  decEq (Leaf k j i) (Leaf a b c)
    = decDo $ do Refl <- decEq k a `otherwise` (\Refl => Refl)
                 Refl <- decEq j b `otherwise` (\Refl => Refl)
                 Refl <- decEq i c `otherwise` (\Refl => Refl)
                 pure Refl

  export
  DecEq Vertex where
    decEq = Vertex.decEq

  namespace API
    public export
    ident : Vertex -> Nat
    ident (Node   k j i) = k
    ident (Leaf f k j)   = k

    public export
    degreeOut : Vertex -> Nat
    degreeOut (Node k j i)   = i
    degreeOut (Leaf SRC k j) = j
    degreeOut (Leaf SNK k j) = 0
    degreeOut (Leaf BI k j)  = j

    public export
    degreeIn : Vertex -> Nat
    degreeIn (Node k j i)   = j
    degreeIn (Leaf SRC k j) = 0
    degreeIn (Leaf SNK k j) = j
    degreeIn (Leaf BI k j)  = j


    export
    driver : Nat -> Nat -> Vertex
    driver = Leaf SRC

    export
    catcher : Nat -> Nat -> Vertex
    catcher = Leaf SNK

    export
    gateway : Nat -> Nat -> Vertex
    gateway = Leaf BI

    export
    node : Nat -> Nat -> Nat -> Vertex
    node = Node

    export
    both : Nat -> Nat -> Vertex
    both i n = Node i n n

namespace Graph

  public export
  Vertices : Type
  Vertices = List Vertex

  public export
  Edge : Type
  Edge = Pair Nat Nat

  public export
  Edges : Type
  Edges = List Edge


  public export
  record Graph where
    constructor MkGraph
    nodes : Vertices
    edges : Edges


  public export
  empty : Graph
  empty = MkGraph Nil Nil

  showGraph : Graph -> String
  showGraph (MkGraph nodes edges)
      = unlines $ ["digraph G {"]
                  ++
                    map show nodes
                  ++
                    map (\(x,y) => unwords ["\t" <+> show x, "->", show y <+> ";"]) edges
                  ++
                  ["}"]

  export
  Show Graph where
    show = showGraph

  namespace API

    export
    insertNode : Vertex -> Graph -> Graph
    insertNode k (MkGraph nodes edges) with (isElem k nodes)
      insertNode k (MkGraph nodes edges) | (Yes prf)
        = MkGraph nodes edges
      insertNode k (MkGraph nodes edges) | (No contra)
        = MkGraph (k::nodes) edges


    export
    insertEdge : (Nat, Nat) -> Graph -> Graph
    insertEdge (a, b) (MkGraph nodes edges) with (isElem (a,b) edges)
      insertEdge (a, b) (MkGraph nodes edges) | (Yes prf)
        = MkGraph nodes edges
      insertEdge (a, b) (MkGraph nodes edges) | (No contra)
        = MkGraph nodes (MkPair a b :: edges)

    from : Graph -> List Vertex -> List (Nat,Nat) -> Graph
    from g nodes
      = foldr insertEdge (foldr insertNode g nodes)

    export
    fromLists : List Vertex -> List (Nat,Nat) -> Graph
    fromLists = from empty


    export
    merge : (a,b : Graph) -> Graph
    merge (MkGraph vs es) g
      = from g vs es

namespace DegreeOut

  public export
  HasDegreeOut : (v  : Nat)
              -> (es : Edges)
              -> (d  : Nat)
                    -> Type
  HasDegreeOut v
    = DoesOccur (Pair Nat Nat) (IsFirst v)


  export
  hasDegreeOut : (v : Nat) -> (es : Edges) -> (d : Nat) -> Dec (HasDegreeOut v es d)
  hasDegreeOut v = doesOccur (isFirst v)

namespace DegreeIn

  public export
  HasDegreeIn : (v  : Nat)
             -> (es : Edges)
             -> (d  : Nat)
                   -> Type
  HasDegreeIn v = DoesOccur (Pair Nat Nat) (IsSecond v)

  export
  hasDegreeIn : (v : Nat) -> (es : Edges) -> (d : Nat) -> Dec (HasDegreeIn v es d)
  hasDegreeIn v = doesOccur (isSecond v)

namespace HasDegree

  namespace Raw

    public export
    data ExpDegrees : (v : Vertex) -> (i,o : Nat) -> Type where
      Node : ExpDegrees (Node     k j i) j i
      Src  : ExpDegrees (Leaf SRC k j)   0 j
      Bsrc : ExpDegrees (Leaf BI  k j)   0 j
      Snk  : ExpDegrees (Leaf SNK k j)   j 0
      Bsnk : ExpDegrees (Leaf BI  k j)   j 0

    public export
    data HasDegree : (v   : Vertex)
                  -> (es  : Edges)
                  -> (i,o : Nat)
                  -> (exp : ExpDegrees v i o)
                         -> Type
      where
        HDN : (din  : HasDegreeIn  v es i)
           -> (dout : HasDegreeOut v es o)
                   -> HasDegree (Node v i o) es i o Node

        HDLS : (din  : HasDegreeIn  v es 0)
            -> (dout : HasDegreeOut v es o)
                    -> HasDegree (Leaf SRC v o) es 0 o Src

        HDLT : (din  : HasDegreeIn  v es i)
            -> (dout : HasDegreeOut v es 0)
                    -> HasDegree (Leaf SNK v i) es i 0 Snk

        HDLBS : (din  : HasDegreeIn  v es 0)
             -> (dout : HasDegreeOut v es k)
                     -> HasDegree (Leaf BI v k) es 0 k Bsrc

        HDLBT : (din  : HasDegreeIn  v es k)
             -> (dout : HasDegreeOut v es 0)
                     -> HasDegree (Leaf BI v k) es k 0 Bsnk



    leafBiAsSrcOutWrong : (HasDegreeOut       k    es   o      -> Void)
                        -> HasDegree (Leaf BI k o) es 0 o Bsrc -> Void
    leafBiAsSrcOutWrong f (HDLBS din dout) = f dout

    leafBiAsSrcInWrong : (HasDegreeIn        k    es 0        -> Void)
                      ->  HasDegree (Leaf BI k o) es 0 o Bsrc -> Void
    leafBiAsSrcInWrong f (HDLBS din dout) = f din

    leafBiAsSnkOutWrong : (HasDegreeOut       k    es   0      -> Void)
                       ->  HasDegree (Leaf BI k o) es o 0 Bsnk -> Void
    leafBiAsSnkOutWrong f (HDLBT din dout) = f dout

    leafBiAsSnkInWrong : (HasDegreeIn        k    es o        -> Void)
                      ->  HasDegree (Leaf BI k o) es o 0 Bsnk -> Void
    leafBiAsSnkInWrong f (HDLBT din dout) = f din

    export
    hasDegree : (v   : Vertex)
             -> (exp : ExpDegrees v i o)
             -> (es  : Edges)
                    -> Dec (HasDegree v es i o exp)

    hasDegree (Node k i o) Node es with (hasDegreeIn k es i)
      hasDegree (Node k i o) Node es | (Yes pI) with (hasDegreeOut k es o)
        hasDegree (Node k i o) Node es | (Yes pI) | (Yes pO)
          = Yes (HDN pI pO)
        hasDegree (Node k i o) Node es | (Yes pI) | (No contra)
          = No (\(HDN pI pO) => contra pO)

      hasDegree (Node k i o) Node es | (No contra)
        = No (\(HDN pI pO) => contra pI)

    hasDegree (Leaf SRC k o) Src es with (hasDegreeIn k es 0)
      hasDegree (Leaf SRC k o) Src es | (Yes pI) with (hasDegreeOut k es o)
        hasDegree (Leaf SRC k o) Src es | (Yes pI) | (Yes pO)
          = Yes (HDLS pI pO)
        hasDegree (Leaf SRC k o) Src es | (Yes pI) | (No contra)
          = No (\(HDLS pI pO) => contra pO)
      hasDegree (Leaf SRC k o) Src es | (No contra)
        = No (\(HDLS pI pO) => contra pI)

    hasDegree (Leaf BI k o) Bsrc es with (hasDegreeIn k es 0)
      hasDegree (Leaf BI k o) Bsrc es | (Yes pI) with (hasDegreeOut k es o)
        hasDegree (Leaf BI k o) Bsrc es | (Yes pI) | (Yes pO)
          = Yes (HDLBS pI pO)
        hasDegree (Leaf BI k o) Bsrc es | (Yes pI) | (No contra)
          = No (leafBiAsSrcOutWrong contra)

      hasDegree (Leaf BI k o) Bsrc es | (No contra)
        = No (leafBiAsSrcInWrong contra)

    hasDegree (Leaf SNK k i) Snk es with (hasDegreeIn k es i)
      hasDegree (Leaf SNK k i) Snk es | (Yes pI) with (hasDegreeOut k es 0)
        hasDegree (Leaf SNK k i) Snk es | (Yes pI) | (Yes pO)
          = Yes (HDLT pI pO)
        hasDegree (Leaf SNK k i) Snk es | (Yes pI) | (No contra)
          = No (\(HDLT pI pO) => contra pO)

      hasDegree (Leaf SNK k i) Snk es | (No contra)
        = No (\(HDLT pI pO) => contra pI)

    hasDegree (Leaf BI k i) Bsnk es with (hasDegreeIn k es i)
      hasDegree (Leaf BI k i) Bsnk es | (Yes pO) with (hasDegreeOut k es 0)
        hasDegree (Leaf BI k i) Bsnk es | (Yes pO) | (Yes pI)
          = Yes (HDLBT pO pI)
        hasDegree (Leaf BI k i) Bsnk es | (Yes pO) | (No contra)
          = No (leafBiAsSnkOutWrong contra)

      hasDegree (Leaf BI k i) Bsnk es | (No contra)
        = No (leafBiAsSnkInWrong contra)


  public export
  data HasDegree : (v : Vertex) -> (es : Edges) -> Type where
    R : (exp : ExpDegrees v i o)
     -> (prf : HasDegree v es i o exp)
            -> HasDegree v es


  biLeafWrong : (HasDegree (Leaf BI k j) es j 0 Bsnk -> Void)
             -> (HasDegree (Leaf BI k j) es 0 j Bsrc -> Void)
             ->  HasDegree (Leaf BI k j) es          -> Void
  biLeafWrong f g (R Bsrc prf) = g prf
  biLeafWrong f g (R Bsnk prf) = f prf

  export
  hasDegree : (v : Vertex) -> (es : Edges) -> Dec (HasDegree v es)

  hasDegree (Node k j i) es with (hasDegree (Node k j i) Node es)
    hasDegree (Node k j i) es | (Yes prf)
      = Yes (R Node prf)
    hasDegree (Node k j i) es | (No contra)
      = No (\(R Node prf) => contra prf)

  hasDegree (Leaf SRC k j) es with (hasDegree (Leaf SRC k j) Src es)
    hasDegree (Leaf SRC k j) es | (Yes prf)
      = Yes (R Src prf)
    hasDegree (Leaf SRC k j) es | (No contra)
      = No (\(R Src prf) => contra prf)

  hasDegree (Leaf SNK k j) es with (hasDegree (Leaf SNK k j) Snk es)
    hasDegree (Leaf SNK k j) es | (Yes prf)
      = Yes (R Snk prf)
    hasDegree (Leaf SNK k j) es | (No contra)
      = No (\(R Snk prf) => contra prf)

  hasDegree (Leaf BI k j) es with (hasDegree (Leaf BI k j) Bsrc es)
    hasDegree (Leaf BI k j) es | (Yes prf)
      = Yes (R Bsrc prf)

    hasDegree (Leaf BI k j) es | (No contra) with (hasDegree (Leaf BI k j) Bsnk es)
      hasDegree (Leaf BI k j) es | (No contra) | (Yes prf)
        = Yes (R Bsnk prf)

      hasDegree (Leaf BI k j) es | (No contra) | (No f)
        = No (biLeafWrong f contra)


  public export
  HasDegrees : List Vertex -> Edges -> Type
  HasDegrees vs es = All (\v => HasDegree v es) vs

  export
  hasDegrees : (vs : List Vertex) -> (es : Edges) -> Dec (HasDegrees vs es)
  hasDegrees vs es = all (\v => hasDegree v es) vs


namespace Properties
  public export
  data ValidGraph : Graph -> Type where
    IsValid : HasDegrees vs es
           -> ValidGraph (MkGraph vs es)

  export
  validGraph : (g : Graph) -> Dec (ValidGraph g)
  validGraph (MkGraph nodes edges) with (hasDegrees nodes edges)
    validGraph (MkGraph nodes edges) | (Yes prf)
      = Yes (IsValid prf)
    validGraph (MkGraph nodes edges) | (No contra)
      = No (\(IsValid prf) => contra prf)

test0 : Graph
test0 = fromLists [ Leaf SRC 1 1 , Leaf SNK 2 1 ] [(2,1)]

test1 : Graph
test1 = fromLists [ Leaf SRC 1 1 , Leaf SNK 2 1 ] [(2,1)]

test2 : Graph
test2 = fromLists [ Leaf BI 1 1 , Leaf BI 2 1] [(2,1)]

test3 : Graph
test3 = fromLists [ Leaf BI 1 1 , Leaf BI 2 1] [(1,2)]

test4 : Graph
test4 = fromLists [ Leaf BI 1 1 , Leaf BI 2 1] [(1,2), (2,1)]




-- [ EOF ]
