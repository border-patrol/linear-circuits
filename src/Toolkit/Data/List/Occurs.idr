module Toolkit.Data.List.Occurs

import Decidable.Equality

import Toolkit.Data.Nat
import Toolkit.Data.DList
import Toolkit.Data.List.Size
import Toolkit.Data.List.Interleaving

%default total


public export
data Occurs : (type : Type)
           -> (p    : type -> Type)
           -> (xs   : List type)
           -> (cy   : Nat)
           -> (cn   : Nat)
                   -> Type
   where
     O : (thrown     : List type)
      -> (sizeThrown : Size thrown t)

      -> (kept       : List type)
      -> (sizeKept   : Size kept   k)

      -> (prfOrigin  : Interleaving kept thrown input)

      -> (prfKept    : DList  type        holdsFor  kept)
      -> (prfThrown  : DList  type (Not . holdsFor) throw)

                    -> Occurs type holdsFor input k t

namespace Result

  public export
  data Occurs : (type : Type)
             -> (p    : type -> Type)
             -> (xs   : List type)
                     -> Type
    where
      O : {type  : Type}
       -> {p     : type -> Type}
       -> (xs    : List type)
       -> (cy,cn : Nat)
       -> (prf   : Occurs type p xs cy cn)
                -> Occurs type p xs


export
occurs : {type : Type}
      -> {p    : type -> Type}
      -> (f    : (this : type) -> Dec (p this))
      -> (xs   : List type)
              -> Occurs type p xs
occurs f []
  = O [] 0 0 (O [] Zero [] Zero Empty [] [])

occurs f (x :: xs) with (f x)
  occurs f (x :: xs) | (Yes prf) with (occurs f xs)

    occurs f (x :: xs) | (Yes prf) | (O xs cy cn (O thrown sizeThrown kept sizeKept prfOrigin prfKept prfThrown))
      = O (x::xs) (S cy) cn (O thrown sizeThrown (x :: kept) (PlusOne sizeKept) (Left x prfOrigin) (prf :: prfKept) prfThrown)

  occurs f (x :: xs) | (No not) with (occurs f xs)
    occurs f (x :: xs) | (No not) | (O xs cy cn (O thrown sizeThrown kept sizeKept prfOrigin prfKept prfThrown))
      = O (x::xs) cy (S cn) (O (x :: thrown) (PlusOne sizeThrown) kept sizeKept (Right x prfOrigin) prfKept (not :: prfThrown))


namespace Does

  public export
  data DoesOccur : (type : Type)
                -> (p    : type -> Type)
                -> (xs   : List type)
                -> (cy   : Nat)
                        -> Type
    where
      End : DoesOccur type p Nil Z

      Yes : (holds : p x)
         -> (rest  : DoesOccur type p     xs     cy)
                  -> DoesOccur type p (x::xs) (S cy)

      No : (nope : Not (p x))
        -> (rest : DoesOccur type p     xs  cy)
                -> DoesOccur type p (x::xs) cy

  Uninhabited (DoesOccur type p Nil (S x)) where
    uninhabited End impossible
    uninhabited (Yes holds rest) impossible
    uninhabited (No nope rest) impossible

  shouldHaveOneMore : (p x) -> (DoesOccur type p xs k -> Void) -> DoesOccur type p (x :: xs) (S k) -> Void
  shouldHaveOneMore prf f (Yes holds rest) = f rest
  shouldHaveOneMore prf f (No nope rest) = nope prf

  wrongOccurs : (DoesOccur type p xs cy -> Void) -> (p x -> Void) -> DoesOccur type p (x :: xs) cy -> Void
  wrongOccurs f g (Yes holds rest) = g holds
  wrongOccurs f g (No nope rest) = f rest

  export
  doesOccur : {type : Type}
           -> {p    : type -> Type}
           -> (f    : (this : type) -> Dec (p this))
           -> (xs   : List type)
           -> (cy   : Nat)
                   -> Dec (DoesOccur type p xs cy)
  doesOccur f [] Z
    = Yes End

  doesOccur f [] (S k)
    = No absurd

  doesOccur f (x :: xs) cy with (f x)
    doesOccur f (x :: xs) cy | (Yes prf) with (cy)
      doesOccur f (x :: xs) cy | (Yes prf) | Z
        = No (\(No f x) => f prf)

      doesOccur f (x :: xs) cy | (Yes prf) | (S k) with (doesOccur f xs k)
        doesOccur f (x :: xs) cy | (Yes prf) | (S k) | (Yes y)
          = Yes (Yes prf y)

        doesOccur f (x :: xs) cy | (Yes prf) | (S k) | (No contra)
          = No (shouldHaveOneMore prf contra)

    doesOccur f (x :: xs) cy | (No contra) with (doesOccur f xs cy)
      doesOccur f (x :: xs) cy | (No contra) | (Yes prf)
        = Yes (No contra prf)

      doesOccur f (x :: xs) cy | (No contra) | (No g)
        = No (wrongOccurs g contra)

namespace DoesNot

  public export
  data DoesNotOccur : (type : Type)
                   -> (p    : type -> Type)
                   -> (xs   : List type)
                   -> (cy   : Nat)
                           -> Type
    where
      End : DoesNotOccur type p Nil Z

      Yes : (holds : p x)
         -> (rest  : DoesNotOccur type p     xs  cn)
                  -> DoesNotOccur type p (x::xs) cn

      No : (nope : Not (p x))
        -> (rest : DoesNotOccur type p     xs     cn)
                -> DoesNotOccur type p (x::xs) (S cn)

  Uninhabited (DoesNotOccur type p Nil (S x)) where
    uninhabited End impossible
    uninhabited (Yes holds rest) impossible
    uninhabited (No nope rest) impossible


  shouldBeZero : (p x -> Void) -> DoesNotOccur type p (x :: xs) 0 -> Void
  shouldBeZero f (Yes holds rest) = f holds


  shouldNotOccurMore : (DoesNotOccur type p xs k -> Void) -> (p x -> Void) -> DoesNotOccur type p (x :: xs) (S k) -> Void
  shouldNotOccurMore f g (Yes holds rest) = g holds
  shouldNotOccurMore f g (No nope rest) = f rest

  wrongOccursNot : (DoesNotOccur type p xs cn -> Void) -> p x -> DoesNotOccur type p (x :: xs) cn -> Void
  wrongOccursNot f y (Yes holds rest) = f rest
  wrongOccursNot f y (No nope rest) = nope y

  export
  doesNotOccur : {type : Type}
              -> {p    : type -> Type}
              -> (f    : (this : type) -> Dec (p this))
              -> (xs   : List type)
              -> (cn   : Nat)
                      -> Dec (DoesNotOccur type p xs cn)
  doesNotOccur f [] Z
    = Yes End

  doesNotOccur f [] (S k)
    = No absurd

  doesNotOccur f (x :: xs) cn with (f x)
    doesNotOccur f (x :: xs) cn | (Yes prf) with (doesNotOccur f xs cn)
      doesNotOccur f (x :: xs) cn | (Yes prf) | (Yes y)
        = Yes (Yes prf y)

      doesNotOccur f (x :: xs) cn | (Yes prf) | (No contra)
        = No (wrongOccursNot contra prf)

    doesNotOccur f (x :: xs) cn | (No contra) with (cn)

      doesNotOccur f (x :: xs) cn | (No contra) | 0
        = No (shouldBeZero contra)

      doesNotOccur f (x :: xs) cn | (No contra) | (S k) with (doesNotOccur f xs k)
        doesNotOccur f (x :: xs) cn | (No contra) | (S k) | (Yes prf)
          = Yes (No contra prf)

        doesNotOccur f (x :: xs) cn | (No contra) | (S k) | (No g)
          = No (shouldNotOccurMore g contra)



-- [ EOF ]
