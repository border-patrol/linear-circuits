module Toolkit.Data.Vect.Extra

import public Decidable.Equality
import        Data.Vect

%default total

namespace Equality
   public export
   vecEq : Eq type => Vect n type -> Vect m type -> Bool
   vecEq [] [] = True
   vecEq [] (x :: xs) = False
   vecEq (x :: xs) [] = False
   vecEq (x :: xs) (y :: ys) = x == y && vecEq xs ys

namespace Decidable
  namespace SameLength
    public export
    decEq : DecEq type
          => (n = m)
          -> (xs : Vect n type)
          -> (ys : Vect m type)
          -> Dec (xs = ys)
    decEq Refl xs ys with (decEq xs ys)
      decEq Refl ys ys | (Yes Refl) = Yes Refl
      decEq Refl xs ys | (No contra) = No contra

  namespace DiffLength

    public export
    vectorsDiffLength : DecEq type
                      => (contra : (n = m) -> Void)
                      -> {xs : Vect n type}
                      -> {ys : Vect m type}
                      -> (xs = ys) -> Void
    vectorsDiffLength contra Refl = contra Refl

    public export
    decEq : DecEq type
         => {n,m : Nat}
         -> (xs : Vect n type)
         -> (ys : Vect m type)
         -> Dec (xs = ys)
    decEq xs ys {n} {m} with (decEq n m)
      decEq xs ys {n = m} {m = m} | (Yes Refl) = decEq Refl xs ys
      decEq xs ys {n = n} {m = m} | (No contra) = No (vectorsDiffLength contra)

namespace Shape

  public export
  data Shape : (xs : Vect n a)
            -> (ys : Vect m a)
            -> Type
    where
      Empty : Shape Nil Nil
      LH    : Shape (x::xs) Nil
      RH    : Shape Nil      (y::ys)
      Both  : Shape (x::xs) (y::ys)

  export
  shape : (xs : Vect n a)
       -> (ys : Vect m a)
       -> Shape xs ys
  shape [] [] = Empty
  shape [] (y :: ys) = RH
  shape (x :: xs) [] = LH
  shape (x :: xs) (y :: ys) = Both

namespace ReplaceAt

  public export
  data ReplaceAt : (idx       : Fin n)
                -> (xs        : Vect n a)
                -> (this,that : a)
                -> (ys        : Vect n a)
                             -> Type
    where
      H : ReplaceAt FZ (x::xs)
                        x
                        y
                       (y::xs)

      T : ReplaceAt     idx       xs  x y      ys
       -> ReplaceAt (FS idx) (x'::xs) x y (x'::ys)

  notSame : (x = this -> Void) -> DPair (Vect (S len) a) (ReplaceAt FZ (x :: xs) this that) -> Void
  notSame _ (MkDPair _ (T y)) impossible

  notLater : (DPair (Vect len a) (ReplaceAt x xs this that) -> Void) -> DPair (Vect (S len) a) (ReplaceAt (FS x) (y :: xs) this that) -> Void
  notLater f (MkDPair (y :: ys) (T z)) = f (MkDPair ys z)

  export
  replaceAt : DecEq a
           => (idx : Fin n)
           -> (xs  : Vect n a)
           -> (this, that : a)
           -> Dec (DPair (Vect n a) (ReplaceAt idx xs this that))
  replaceAt FZ (x :: xs) this that with (decEq x this)
    replaceAt FZ (x :: xs) x    that | (Yes Refl) = Yes (MkDPair (that :: xs) H)
    replaceAt FZ (x :: xs) this that | (No contra)
      = No (notSame contra)
  replaceAt (FS x) (y :: xs) this that with (replaceAt x xs this that)
    replaceAt (FS x) (y :: xs) this that | (Yes (MkDPair fst snd))
      = Yes (MkDPair (y :: fst) (T snd))
    replaceAt (FS x) (y :: xs) this that | (No contra)
      = No (notLater contra)

-- [ EOF ]
