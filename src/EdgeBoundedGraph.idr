||| A graph whose vertices have a restricted in/out degree.
module EdgeBoundedGraph

import Decidable.Equality

import Data.List.Elem
import Data.List.Quantifiers

import Utilities

public export
record Vertex where
  constructor Node
  ident : Nat
  degreeIn : Nat
  degreeOut : Nat

public export
AList : Type
AList = List (Nat, List Nat)


export
driver : Nat -> Vertex
driver k = Node k 0 1

export
catcher : Nat -> Vertex
catcher k = Node k 1 0

public export
decEq : (a,b : Vertex) -> Dec (a = b)
decEq (Node x y z) (Node a b c) with (decEq x a)
  decEq (Node x y z) (Node x b c) | (Yes Refl) with (decEq y b)
    decEq (Node x y z) (Node x y c) | (Yes Refl) | (Yes Refl) with (decEq z c)
      decEq (Node x y z) (Node x y z) | (Yes Refl) | (Yes Refl) | (Yes Refl)
        = Yes Refl

      decEq (Node x y z) (Node x y c) | (Yes Refl) | (Yes Refl) | (No contra)
        = No (\Refl => contra Refl)
    decEq (Node x y z) (Node x b c) | (Yes Refl) | (No contra)
      = No (\Refl => contra Refl)

  decEq (Node x y z) (Node a b c) | (No contra)
    = No (\Refl => contra Refl)

export
DecEq Vertex where
 decEq = EdgeBoundedGraph.decEq


public export
data DegreeOut : Nat -> (alist : AList) -> (d : Nat) -> Type where
  NotOut    : DegreeOut v Nil Z
  DOut      : Size es k -> DegreeOut v ((v,es) :: rest) k
  NotHere   : DegreeOut v           rest  k
           -> DegreeOut v (not_v :: rest) k


degreeOutZ : (d = 0 -> Void) -> DegreeOut v [] d -> Void
degreeOutZ f NotOut = f Refl

degreeOutWrongJust : (DegreeOut v xs d -> Void) -> (v = x -> Void) -> DegreeOut v ((x, y) :: xs) d -> Void
degreeOutWrongJust f g (DOut z) = g Refl
degreeOutWrongJust f g (NotHere z) = f z

degreeOutnotFound : (DegreeOut v xs d -> Void) -> (Size y d -> Void) -> DegreeOut v ((v, y) :: xs) d -> Void
degreeOutnotFound f g (DOut x) = g x
degreeOutnotFound f g (NotHere x) = f x

export
degreeOut : (v  : Nat)
         -> (d  : Nat)
         -> (es : AList)
               -> Dec (DegreeOut v es d)
degreeOut v d [] with (decEq d Z)
  degreeOut v 0 [] | (Yes Refl)
    = Yes NotOut
  degreeOut v d [] | (No contra)
    = No (degreeOutZ contra)

degreeOut v d ((x,y) :: xs) with (decEq v x)
  degreeOut v d ((v,y) :: xs) | (Yes Refl) with (hasSize y d)
    degreeOut v d ((v,y) :: xs) | (Yes Refl) | (Yes prf)
      = Yes (DOut prf)

    -- [ NOTE ] we need the recursive step as we are dealing with list's not sets.
    degreeOut v d ((v,y) :: xs) | (Yes Refl) | (No contra) with (degreeOut v d xs)
      degreeOut v d ((v,y) :: xs) | (Yes Refl) | (No contra) | (Yes prf)
        = Yes (NotHere prf)
      degreeOut v d ((v,y) :: xs) | (Yes Refl) | (No contra) | (No f)
        = No (degreeOutnotFound f contra)

  degreeOut v d ((x,y) :: xs) | (No contra) with (degreeOut v d xs)
    degreeOut v d ((x,y) :: xs) | (No contra) | (Yes prf)
      = Yes (NotHere prf)
    degreeOut v d ((x,y) :: xs) | (No contra) | (No f)
      = No (degreeOutWrongJust f contra)


public export
data DegreeIn : (v : Nat) -> (alist : AList) -> (d : Nat) -> Type where
  NotIn : DegreeIn v Nil Z
  Found : Elem           v              es
       -> DegreeIn v                rest     k
       -> DegreeIn v ((not_v,es) :: rest) (S k)

  Later : Not (Elem v es)
       -> DegreeIn v rest k
       -> DegreeIn v (((not_v), es) :: rest) k

shouldBeZero : Elem v y -> DegreeIn v ((x, y) :: xs) 0 -> Void
shouldBeZero z (Later f _) = f z

shouldBeZeroCons : (DegreeIn v xs 0 -> Void) -> DegreeIn v ((x, y) :: xs) 0 -> Void
shouldBeZeroCons f (Later _ z) = f z

notInLaterFound : (DegreeIn v            xs     k  -> Void)
               -> (Elem     v      y)
               ->  DegreeIn v ((x, y) :: xs) (S k) -> Void
notInLaterFound f _ (Found _ s) = f s
notInLaterFound _ z (Later g _) = g z


notInLaterLater : (DegreeIn v xs             (S k) -> Void)
               -> (Elem     v      y               -> Void)
               -> DegreeIn  v ((x, y) :: xs) (S k) -> Void
notInLaterLater _ g (Found z _) = g z
notInLaterLater f _ (Later _ z) = f z

export
degreeIn : (v  : Nat)
        -> (i  : Nat)
        -> (es : AList)
              -> Dec (DegreeIn v es i)
degreeIn v i [] with (decEq i Z)
  degreeIn v Z [] | (Yes Refl)
    = Yes NotIn
  degreeIn v i [] | (No contra)
    = No (\NotIn => contra Refl)

degreeIn v 0 ((x, y) :: xs) with (isElem v y)
  degreeIn v 0 ((x, y) :: xs) | (Yes prf) = No (shouldBeZero prf)

  degreeIn v 0 ((x, y) :: xs) | (No contra) with (degreeIn v 0 xs)
    degreeIn v 0 ((x, y) :: xs) | (No contra) | (Yes prf)
      = Yes (Later contra prf) -- [ NOTE ] Should be Zero all the way down.
    degreeIn v 0 ((x, y) :: xs) | (No contra) | (No f)
      = No (shouldBeZeroCons f)

degreeIn v (S k) ((x, y) :: xs) with (isElem v y)
  degreeIn v (S k) ((x, y) :: xs) | (Yes prf) with (degreeIn v k xs)
    degreeIn v (S k) ((x, y) :: xs) | (Yes prf) | (Yes z)
      = Yes (Found prf z)

    degreeIn v (S k) ((x, y) :: xs) | (Yes prf) | (No contra)
      = No (notInLaterFound contra prf)

  degreeIn v (S k) ((x, y) :: xs) | (No contra) with (degreeIn v (S k) xs)
    degreeIn v (S k) ((x, y) :: xs) | (No contra) | (Yes prf)
      = Yes (Later contra prf)
    degreeIn v (S k) ((x, y) :: xs) | (No contra) | (No f)
      = No (notInLaterLater f contra)

public export
data HasDegree : Vertex -> (es : AList) -> (i,o : Nat) -> Type where
  HD : (din  : DegreeIn  v es i)
    -> (dout : DegreeOut v es o)
            -> HasDegree (Node v i o) es i o


vertexDegOutWrong : (DegreeOut       v      es   o -> Void)
                  -> HasDegree (Node v i o) es i o -> Void
vertexDegOutWrong f (HD _ dout) = f dout

vertexDegInWrong : (DegreeIn        v      es i   -> Void)
                 -> HasDegree (Node v i o) es i o -> Void
vertexDegInWrong f (HD din _) = f din

export
hasDegree : (v  : Vertex)
         -> (es : AList)
               -> Dec (HasDegree v es (degreeIn v) (degreeOut v))
hasDegree (Node v i o) es with (degreeOut v o es)
  hasDegree (Node v i o) es | (Yes prf) with (degreeIn v i es)
    hasDegree (Node v i o) es | (Yes prf) | (Yes x)
      = Yes (HD x prf)
    hasDegree (Node v i o) es | (Yes prf) | (No contra)
      = No (vertexDegInWrong contra)
  hasDegree (Node v i o) es | (No contra)
    = No (vertexDegOutWrong contra)

public export
HasDegrees : List Vertex -> AList -> Type
HasDegrees vs es = All (\v => HasDegree v es (degreeIn v) (degreeOut v)) vs

hasDegrees : (vs : List Vertex) -> (es : AList) -> Dec (HasDegrees vs es)
hasDegrees vs es = all (\vs => hasDegree vs es) vs


public export
data Graph : Type where
  MkGraph : (nodes : List Vertex)
         -> (edges : AList)
                  -> Graph

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

export
insertNode : Vertex -> Graph -> Graph
insertNode k (MkGraph nodes edges) with (isElem k nodes)
  insertNode k (MkGraph nodes edges) | (Yes prf) = MkGraph nodes edges
  insertNode k (MkGraph nodes edges) | (No contra) = MkGraph (k::nodes) edges


insertEdge' : Nat -> Nat -> AList -> AList
insertEdge' k j [] = [(k,[j])]
insertEdge' k j ((k',es) :: xs) with (decEq k k')
  insertEdge' k j ((k,es) :: xs) | (Yes Refl) = (k,j::es) :: xs
  insertEdge' k j ((k',es) :: xs) | (No contra) = (k',es) :: insertEdge' k j xs

export
insertEdge : (Nat, Nat) -> Graph -> Graph
insertEdge (a, b) (MkGraph nodes edges) = MkGraph nodes (insertEdge' a b edges)


-- [ EOF ]
