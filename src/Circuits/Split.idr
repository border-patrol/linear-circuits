module Circuits.Split

import Decidable.Equality
import Data.Nat

import Toolkit.Decidable.Informative
import Toolkit.Data.Whole

%default total

namespace EdgeCase

  ||| Index for indexing the first and last elements.
  |||
  ||| These will result in a *single* free vector returned.
  public export
  data Index : (vSize : Whole)
            -> (idx   : Nat)
            -> (free  : Whole)
                     -> Type
    where
      ||| Edgecase for a pivot of value 0, implies that the length of vector is >=2
      First : Index (W (S (S n)) ItIsSucc)
                             Z
                    (W    (S n)  ItIsSucc)
      ||| Edgecase for a vector with length >= 2 where pivot is length - 1
      Last  : Index (W (S (S n)) ItIsSucc)
                          (S n)
                    (W    (S n)  ItIsSucc)

  Uninhabited (s ** Index (W (S Z) ItIsSucc) pivot s) where
    uninhabited (MkDPair _ _) impossible

  urgh : (S k = S j -> Void) -> DPair Whole (\s => Index (W (S (S k)) ItIsSucc) (S j) s) -> Void
  urgh f (MkDPair (W (S j) ItIsSucc) Last) = f Refl
--

  public export
  data Error = VectIsOne
             | InvalidPivot Nat Nat

  export
  index : (size  : Whole)
       -> (pivot : Nat)
                -> DecInfo Error (s ** Index size pivot s)

  -- [ NOTE ] Vector of length cannot be indexed with remaining slots
  index (W (S 0) ItIsSucc) 0
    = No VectIsOne absurd

  -- [ NOTE ] Selecting first element
  index (W (S (S k)) ItIsSucc) 0
    = Yes (MkDPair (W (S k) ItIsSucc) First)

  -- [ NOTE ] Selecting last element
  index (W (S 0) ItIsSucc) (S j)
    = No VectIsOne absurd

  index (W (S (S k)) ItIsSucc) (S j) with (decEq (S k) (S j))
    index (W (S (S k)) ItIsSucc) (S k) | (Yes Refl)
      = Yes (MkDPair (W (S k) ItIsSucc) Last)
    index (W (S (S k)) ItIsSucc) (S j) | (No contra)
      = No (InvalidPivot (S j) (S (S k))) (urgh contra)

namespace Pivot

  ||| Index a vector such that we return the length of the unused vectors to the left and right of the pivot.
  |||
  ||| We decrement the pivot until we reach the position in the vector we require.
  ||| For the left half we increment from zero.
  ||| For the right half we decrement from the length of the vector.
  public export
  data Index : (left_counter  : Nat)
            -> (pivot         : Nat)
            -> (right_counter : Whole)
            -> (a,b : Whole) -- results
                     -> Type
    where
      ||| Stop counting when we reach the pivot.
      |||
      ||| The stopping condition is that:
      |||
      ||| + The left half is at least one;
      ||| + The right half is at least one;
      ||| + This implies that the vector is at least length three;
      |||
      Stop : Index (S l)              -- left of pivot
                   Z                  -- empty pivot
                   (W (S (S r)) ItIsSucc) -- right of pivot
                   (W    (S l)  ItIsSucc)
                   (W    (S r)  ItIsSucc)

      ||| Reduce the size of the pivot, and update the counters.
      Step : Index (S l)   p  (W    (S r)  ItIsSucc) a b
          -> Index    l (S p) (W (S (S r)) ItIsSucc) a b

  Uninhabited ((a ** b ** Index Z Z r a b)) where
    uninhabited (MkDPair _ (MkDPair _ _)) impossible

  Uninhabited ((a ** b ** Index l (S p) (W (S Z) ItIsSucc) a b)) where
    uninhabited (MkDPair _ (MkDPair _ _)) impossible

  Uninhabited ((a ** b ** Index (S l) Z (W (S Z) ItIsSucc) a b)) where
    uninhabited (MkDPair _ (MkDPair _ _)) impossible

  public export
  data Error = IsEdgeCase | OutOfBounds

  outOfFuel : ((a ** b ** Index (S l)    k  (W    (S j)  ItIsSucc) a b) -> Void)
           ->  (a ** b ** Index    l  (S k) (W (S (S j)) ItIsSucc) a b) -> Void
  outOfFuel contra (MkDPair a (MkDPair b (Step x))) = contra (MkDPair a (MkDPair b x))

  index' : (l,p : Nat)
        -> (r   : Whole)
               -> DecInfo Pivot.Error (a ** b ** Index l p r a b)

  index' 0 Z r
    = No IsEdgeCase absurd

  index' (S k) Z (W (S Z) ItIsSucc)
    = No IsEdgeCase absurd

  index' (S k) Z (W (S (S j)) ItIsSucc)
    = Yes (MkDPair (W (S k) ItIsSucc) (MkDPair (W (S j) ItIsSucc) Stop))

  index' l (S k) (W (S 0) ItIsSucc)
    = No OutOfBounds absurd

  index' l (S k) (W (S (S j)) ItIsSucc) with (index' (S l) k (W (S j) ItIsSucc))
    index' l (S k) (W (S (S j)) ItIsSucc) | (Yes (MkDPair a (MkDPair b prf)))
      = Yes (MkDPair a (MkDPair b (Step prf)))

    index' l (S k) (W (S (S j)) ItIsSucc) | (No msgWhyNot prfWhyNot)
      = No msgWhyNot (outOfFuel prfWhyNot)

  export
  index : (p : Nat)
       -> (r : Whole)
            -> DecInfo Pivot.Error (a ** b ** Index Z p r a b)
  index = index' Z

namespace Join

  public export
  data Plus : (a,b,c : Nat) -> Type where
    Stop : Plus Z b b
    Step : Plus    a  b    c
        -> Plus (S a) b (S c)

  export
  plus : (a,b : Nat) -> DPair Nat (Plus a b)
  plus Z b
    = MkDPair b Stop
  plus (S k) b with (Join.plus k b)
    plus (S 0) b | (MkDPair b Stop)
      = MkDPair (S b) (Step Stop)

    plus (S (S a)) b | (MkDPair (S c) (Step x))
      = MkDPair (S (S c)) (Step (Step x))

  errWhenZ : (b = c -> Void) -> Plus 0 b c -> Void
  errWhenZ f Stop = f Refl

  cIsZero : Plus (S k) b 0 -> Void
  cIsZero Stop impossible
  cIsZero (Step x) impossible

  errIsLater : (Plus k b j -> Void) -> Plus (S k) b (S j) -> Void
  errIsLater f (Step x) = f x

  export
  isPlus : (a,b,c : Nat) -> Dec (Plus a b c)
  isPlus Z b c with (decEq b c)
    isPlus Z b b | (Yes Refl)
      = Yes Stop

    isPlus Z b c | (No contra)
      = No (errWhenZ contra)

  isPlus (S k) b 0
    = No cIsZero

  isPlus (S k) b (S j) with (isPlus k b j)
    isPlus (S k) b (S j) | (Yes prf)
      = Yes (Step prf)

    isPlus (S k) b (S j) | (No contra)
      = No (errIsLater contra)

  namespace Whole
    public export
    data Plus : (a,b,c : Whole) -> Type where
      P : (comp : Join.Plus (S a) (S b) (S c))
               -> Plus (W (S a) ItIsSucc)
                       (W (S b) ItIsSucc)
                       (W (S c) ItIsSucc)
    export
    plus : (a,b : Whole) -> DPair Whole (Plus a b)
    plus (W (S n) ItIsSucc) (W (S j) ItIsSucc) with (Join.plus n (S j))
      plus (W (S n) ItIsSucc) (W (S j) ItIsSucc) | (MkDPair c prf)
        = (W (S c) ItIsSucc ** P (Step prf))

    isNotPlus : (Plus (S a) (S b) (S c) -> Void) -> Plus (W (S a) ItIsSucc) (W (S b) ItIsSucc) (W (S c) ItIsSucc) -> Void
    isNotPlus f (P comp) = f comp

    export
    isPlus : (a,b,c : Whole) -> Dec (Plus a b c)
    isPlus (W (S a) ItIsSucc) (W (S b) ItIsSucc) (W (S c) ItIsSucc) with (isPlus (S a) (S b) (S c))
      isPlus (W (S a) ItIsSucc) (W (S b) ItIsSucc) (W (S c) ItIsSucc) | (Yes prf)
        = Yes (P prf)
      isPlus (W (S a) ItIsSucc) (W (S b) ItIsSucc) (W (S c) ItIsSucc) | (No contra)
        = No (isNotPlus contra)

-- [ EOF ]
