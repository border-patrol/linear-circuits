module Circuits.Split

import Decidable.Equality
import Data.Nat

%default total

namespace Edgecases
  public export
  data Index : (vSize : Nat)
            -> (idx   : Nat)
            -> (free  : Nat)
                     -> Type
    where
      First2 : Index (S (S Z)) Z (S Z)

      First : Index (S (S n)) Z n
      Last  : Index (S (S n)) n n

  Uninhabited (s ** Index Z pivot s) where
    uninhabited (MkDPair _ _) impossible

  Uninhabited (s ** Index (S Z) pivot s) where
    uninhabited (MkDPair _ _) impossible

  urgh : (k = S j -> Void) -> DPair Nat (\s => Index (S (S k)) (S j) s) -> Void
  urgh f (MkDPair (S j) Last) = f Refl

  export
  index : (size,pivot : Nat) -> Dec (s ** Index size pivot s)
  index 0 pivot = No absurd
  index (S 0) pivot = No absurd

  index (S (S Z)) 0 = Yes (MkDPair _ First2)
  index (S (S k)) 0 = Yes (MkDPair k First)

  index (S (S k)) (S j) with (decEq k (S j))
    index (S (S (S j))) (S j) | (Yes Refl) = Yes (MkDPair (S j) Last)
    index (S (S k)) (S j) | (No contra) = No (urgh contra)

namespace CasesSplit

  public export
  data Index : (l,p,r,a,b : Nat)
                     -> Type
    where
      Stop : Index (S l)     -- left of pivot
                   Z         -- empty pivot
                   (S (S r)) -- right of pivot
                   (S l)
                   (S r)
      Step : Index (S l)   p     r  a b
          -> Index    l (S p) (S r) a b

  Uninhabited ((a ** b ** Index l (S p) Z a b)) where
    uninhabited (MkDPair _ (MkDPair _ _)) impossible

  Uninhabited ((a ** b ** Index l Z Z a b)) where
    uninhabited (MkDPair _ (MkDPair _ _)) impossible

  Uninhabited ((a ** b ** Index l Z (S Z) a b)) where
    uninhabited (MkDPair _ (MkDPair _ _)) impossible

  Uninhabited ((a ** b ** Index Z Z r a b)) where
    uninhabited (MkDPair _ (MkDPair _ _)) impossible

  notEnoughFuel : (DPair Nat (\a => DPair Nat (\b => Index (S l) k j a b)) -> Void) -> DPair Nat (\a => DPair Nat (\b => Index l (S k) (S j) a b)) -> Void
  notEnoughFuel f (MkDPair a (MkDPair b (Step prf))) = f (MkDPair a (MkDPair b prf))

  export
  index : (l,p,r : Nat) -> Dec (a ** b ** Index l p r a b)
  index l 0 0     = No absurd
  index l 0 (S Z) = No absurd
  index 0 0    _  = No absurd

  index (S j) 0 (S (S k)) = Yes (MkDPair (S j) (MkDPair (S k) Stop))

  index l (S k) 0 = No absurd

  index l (S k) (S j) with (index (S l) k j)
    index l (S k) (S j) | (Yes (MkDPair a (MkDPair b prf)))
      = Yes (MkDPair a (MkDPair b (Step prf)))
    index l (S k) (S j) | (No contra) = No (notEnoughFuel contra)

-- [ EOF ]
