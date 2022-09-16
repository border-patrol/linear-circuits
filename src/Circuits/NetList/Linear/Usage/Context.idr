|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Context

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String
import public Data.Singleton

import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

import Circuits.NetList.Linear.Context

import Circuits.NetList.Linear.Usage.DataType
import Circuits.NetList.Linear.Usage.DataType.Use.Full
import Circuits.NetList.Linear.Usage.DataType.Use.Partial

import Circuits.NetList.Linear.Usage.TermType
import Circuits.NetList.Linear.Usage.TermType.Port
import Circuits.NetList.Linear.Usage.TermType.Port.Use
import Circuits.NetList.Linear.Usage.TermType.Channel
import Circuits.NetList.Linear.Usage.TermType.Channel.Use

import Circuits.NetList.Linear.Usage.Item.Port
import Circuits.NetList.Linear.Usage.Item.Channel

%default total

namespace List

  namespace Elem

    namespace Satisied
      public export
      data Elem : (p  : type -> Type)
               -> (x  : type)
               -> (xs : List type)
                     -> Type
        where
          Here : (prfSame : x = y)
              -> (prfSat  : p y)
                         -> Elem p x (y::xs)

          There : (rest : Elem p x     xs)
                       -> Elem p x (y::xs)

      public export
      data ElemNot : (n,p :      type -> Type)
                  -> (x   :      type)
                  -> (xs  : List type)
                         -> Type
        where
          Empty : ElemNot n p x Nil
          HereNot : (prfSame : x = y)
                 -> (prfNeg  : n y)
                 -> (prfNo   : p y -> Void)
                            -> ElemNot n p x (y::xs)

          ThereNotEq : (no : x = y)
                    -> (pNeg : n y)
                    -> (pNo  : p y -> Void)
                    -> (rest : ElemNot n p x     xs)
                            -> ElemNot n p x (y::xs)

          ThereNot : (no : x = y -> Void)
                  -> (rest : ElemNot n p x     xs)
                          -> ElemNot n p x (y::xs)

      Uninhabited (Elem p x Nil) where
        uninhabited (Here prfSame prfSat) impossible

      export
      elemSat : {n,p : type -> Type}
             -> DecEq type
             => (f  : (x : type) -> DecInfo (n x) (p x))
             -> (x  :      type)
             -> (xs : List type)
                   -> DecInfo (ElemNot n p x xs)
                              (Elem      p x xs)
      elemSat f x []
        = No Empty absurd


      elemSat f x (y :: xs) with (decEq x y)
        -- [ NOTE ] Case elements are the same
        elemSat f x (x :: xs) | (Yes Refl) with (f x)
          elemSat f x (x :: xs) | (Yes Refl) | (Yes prf)
            = Yes (Here Refl prf)
          elemSat f x (x :: xs) | (Yes Refl) | (No msg no) with (elemSat f x xs)
            elemSat f x (x :: xs) | (Yes Refl) | (No msg no) | (Yes prf)
              = Yes (There prf)
            -- [ NOTE ] Element might be satisfied elsewhere.
            elemSat f x (x :: xs) | (Yes Refl) | (No msg no) | (No msgT noT)
              = No (HereNot Refl msg no)
                   (\case
                      (Here Refl prfSat) => no prfSat
                      (There rest) => noT rest)

        -- [ NOTE ] Element might be satisfied elsewhere.
        elemSat f x (y :: xs) | (No noEq) with (elemSat f x xs)
          elemSat f x (y :: xs) | (No noEq) | (Yes prf)
            = Yes (There prf)
          elemSat f x (y :: xs) | (No noEq) | (No msg no)
            = No (ThereNot noEq msg)
                 (\case
                    (Here Refl prfSat) => noEq Refl
                    (There rest) => no rest)


      public export
      data Update : (o,n : type -> Type)
                 -> (use : (x    : type)
                        -> (prfO : o x)
                        -> (y    : type)
                        -> (prfN : n y)
                                -> Type)
                 -> (old : List type)
                 -> (prf : Elem o x old)
                 -> (new : List type)
                        -> Type
        where
          UpdateHere : {0 u : (x  : type)
                           -> (pO : o x)
                           -> (y  : type)
                           -> (pN : n y)
                                 -> Type}
                    -> (use : u x pX y pY)

                    -> Update o n u
                              (x::xs)
                              (Here Refl pX)
                              (y::xs)
          UpdateThere : (rest : Update o n u     xs         later      ys)
                             -> Update o n u (x::xs) (There later) (x::ys)

      export
      update : {o,n : type -> Type}
            -> {u   : (x    : type)
                   -> (prfO : o x)
                   -> (y    : type)
                   -> (prfN : n y)
                           -> Type}
            -> (use : {x    : type}
                   -> (prfO : o x)
                           -> (y    : type **
                               prfN : n y  ** u x prfO y prfN))
            -> (old : List type)
            -> (prf : Elem o x old)
                   -> (new ** Update o n u old prf new)
      update use (x :: xs) (Here Refl prf) with (use prf)
        update use (x :: xs) (Here Refl prf) | (y ** (pY ** pU))
          = (y :: xs ** UpdateHere pU)

      update use (y :: xs) (There rest) with (update use xs rest)
        update use (y :: xs) (There rest) | (new ** prfR)
          = (y :: new ** UpdateThere prfR)

namespace Gate

  ||| Construction of this will during type-checking...
  public export
  IsGate : (item : Item)
        -> (ctxt : List Item)
                -> Type

  IsGate
    = Elem IsGate

namespace Chan

  ||| Construction of this will during type-checking...
  public export
  IsChan : (item : Item)
        -> (ctxt : List Item)
                -> Type

  IsChan
    = Elem IsChan

namespace HasType
  public export
  HasType : (type : Ty) -> (item : Item) -> (ctxt : List Item) -> Type
  HasType type
    = Elem (HasType type)

namespace Port

   ||| Construction of this will during type-checking...
   public export
   IsFreePort : (item : Item)
             -> (ctxt : List Item)
                     -> Type
   IsFreePort
     = Elem Port.IsFree

   ||| Construction of this will during type-checking...
   public export
   IsFreePortNot : (item : Item)
             -> (ctxt : List Item)
                     -> Type
   IsFreePortNot
     = Elem Port.IsFreeNot

   public export
   UsePort : (old : List Item)
          -> (prf : IsFreePort item old)
          -> (new : List Item)
                 -> Type
   UsePort old prf new
     = Update Port.IsFree
              Port.IsUsed
              Port.Use
              old
              prf
              new
   export
   usePort : (old : List Item)
          -> (prf : IsFreePort x old)
                 -> DPair (List Item)
                          (Update Port.IsFree
                                  Port.IsUsed
                                  Port.Use
                                  old
                                  prf)
   usePort old prf
       = update embed old prf
     where
       embed : {old  : Item}
            -> (prfO : IsFree old)
                    -> (new  **
                        prfN ** Use old prfO new prfN)
       embed prfO with (Port.use prfO)
         embed prfO | (R prfU u)
           = (_ ** prfU ** u)


   ||| Construction of this will during type-checking...
   public export
   IsFreePortAt : (idx  : List Nat)
               -> (item : Item)
               -> (ctxt : List Item)
                       -> Type
   IsFreePortAt idx
     = Elem (Port.IsFreeAt idx)

   ||| Construction of this will during type-checking...
   public export
   IsFreePortAtNot : (idx  : List Nat)
                  -> (item : Item)
                  -> (ctxt : List Item)
                          -> Type
   IsFreePortAtNot idx
     = Elem (Port.IsFreeAtNot idx)

   public export
   UsePortAt : (idx : List Nat)
            -> (old : List Item)
            -> (prf : IsFreePortAt idx item old)
            -> (new : List Item)
                   -> Type
   UsePortAt idx old prf new
     = Update (Port.IsFreeAt idx)
              (Port.IsUsedAt idx)
              (Port.UseAt    idx)
              old
              prf
              new
   export
   usePortAt : {idx : List Nat}
            -> (old : List Item)
            -> (prf : IsFreePortAt idx x old)
                   -> DPair (List Item)
                            (UsePortAt idx old prf)

   usePortAt {idx} old prf
       = update embed old prf
     where
       embed : {old  : Item}
            -> (prfO : IsFreeAt idx old)
                    -> (new  **
                        prfN ** UseAt idx old prfO new prfN)
       embed prfO with (Port.useAt prfO)
         embed prfO | (R n prfU u)
           = (n ** prfU ** u)

namespace Channel

   ||| Construction of this will during type-checking...
   public export
   CanProject : (how  : Project dir)
             -> (item : Item)
             -> (ctxt : List Item)
                     -> Type
   CanProject how
     = Elem (Channel.CanProject how)

   public export
   CanProjectNot : (how  : Project dir)
                -> (item : Item)
                -> (ctxt : List Item)
                        -> Type
   CanProjectNot how
     = Elem (Channel.CanProjectNot how)


   public export
   UseChannel : (how : Project dir)
             -> (old : List Item)
             -> (prf : CanProject how item old)
             -> (new : List Item)
                    -> Type
   UseChannel how old prf new
     = Update (CanProject how)
              Singleton
              (Channel.Use how)
              old
              prf
              new
   export
   useChannel : {how : Project dir}
             -> (old : List Item)
             -> (prf : CanProject how type old)
                    -> DPair (List Item)
                             (UseChannel how old prf)
   useChannel old prf
       = update embed old prf
    where
      embed : {old  : Item}
           -> (prfO : Channel.CanProject how old)
                   -> (new ** prfN ** Channel.Use how old prfO new prfN)
      embed prfO with (use prfO)
        embed prfO | (R use) = (_ ** _ ** use)

   ||| Construction of this will during type-checking...
   public export
   CanProjectAt : (how  : Project dir)
               -> (idx  : List Nat)
               -> (item : Item)
               -> (ctxt : List Item)
                       -> Type
   CanProjectAt how idx
     = Elem (Channel.CanProjectAt how idx)

   ||| Construction of this will during type-checking...
   public export
   CanProjectAtNot : (how  : Project dir)
                  -> (idx  : List Nat)
                  -> (item : Item)
                  -> (ctxt : List Item)
                          -> Type
   CanProjectAtNot how idx
     = Elem (Channel.CanProjectAtNot how idx)

   public export
   UseChannelAt : (how : Project dir)
               -> (idx : List Nat)
               -> (old : List Item)
               -> (prf : CanProjectAt how idx item old)
               -> (new : List Item)
                      -> Type
   UseChannelAt how idx old prf new
     = Update (CanProjectAt how idx)
              Singleton
              (UseAt how idx)
              old
              prf
              new
   export
   useChannelAt : {idx : List Nat}
               -> {how : Project dir}
               -> (old : List Item)
               -> (prf : CanProjectAt how idx type old)
                      -> DPair (List Item)
                               (UseChannelAt how idx old prf)
   useChannelAt {idx} old prf
       = update embed old prf
    where
      embed : {old  : Item}
           -> (prfO : Channel.CanProjectAt how idx old)
                   -> (new ** prfN ** Channel.UseAt how idx old prfO new prfN)
      embed prfO with (useAt prfO)
        embed prfO | (R new use) = (_ ** (_ ** use))

public export
data CanStop : (item : Item)
                    -> Type
  where
    TyUnit : CanStop (I TyUnit TyUnit)
    TyGate : CanStop (I TyGate TyGate)
    TyPort : IsUsed                  type           u
         -> CanStop (I (TyPort (flow,type)) (TyPort u))
    TyChan : IsUsed             type          i
          -> IsUsed             type            o
          -> CanStop (I (TyChan type) (TyChan i o))

public export
data CanStopNot : (item : Item)
                       -> Type
  where
    ChanFreeIn  : CanStopNot item
    ChanFreeOut : CanStopNot item
    PortUsed : CanStopNot item

export
canStop : (item : Item)
               -> DecInfo (CanStopNot item)
                          (CanStop    item)

canStop (I TyUnit TyUnit)
  = Yes TyUnit

canStop (I (TyPort (flow, type)) (TyPort u)) with (isUsed u)
  canStop (I (TyPort (flow, type)) (TyPort u)) | (Yes prf)
    = Yes (TyPort prf)
  canStop (I (TyPort (flow, type)) (TyPort u)) | (No msg no)
    = No PortUsed
         (\(TyPort prf) => no prf)

canStop (I (TyChan type) (TyChan ein eout)) with (isUsed ein)
  canStop (I (TyChan type) (TyChan ein eout)) | (Yes pIn) with (isUsed eout)
    canStop (I (TyChan type) (TyChan ein eout)) | (Yes pIn) | (Yes pOut)
      = Yes (TyChan pIn pOut)
    canStop (I (TyChan type) (TyChan ein eout)) | (Yes pIn) | (No msg no)
      = No (ChanFreeOut)
           (\(TyChan pI pO) => no pO)

  canStop (I (TyChan type) (TyChan ein eout)) | (No msg no)
    = No (ChanFreeIn)
           (\(TyChan pI pO) => no pI)


canStop (I TyGate TyGate)
  = Yes TyGate

-- [ EOF ]
