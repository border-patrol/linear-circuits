||| Predicates over channels.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.TermType.Channel

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Quantifiers
import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

import Circuits.NetList.Linear.Usage.DataType
import Circuits.NetList.Linear.Usage.TermType

%default total

-- # [ Free Channels ]

{- [ NOTE ]

We do not need to provide an 'is used' equivalent.
The usage is internal to channels.

-}

-- ## [ Positive Predicates ]

public export
data CanProject : (how  : Project dir)
               -> (type : Ty)
               -> (u    : Usage type)
                       -> Type
  where
    ProjectWrite : (prf : IsFree                   type          ein)
                       -> CanProject WRITE (TyChan type) (TyChan ein eout)

    ProjectRead : (prf : IsFree                  type              eout)
                      -> CanProject READ (TyChan type) (TyChan ein eout)

Uninhabited (CanProject how TyGate u) where
  uninhabited (ProjectWrite prf) impossible
  uninhabited (ProjectRead prf) impossible

Uninhabited (CanProject how TyUnit u) where
  uninhabited (ProjectWrite prf) impossible
  uninhabited (ProjectRead prf) impossible

Uninhabited (CanProject how (TyPort (f,dtype)) u) where
  uninhabited (ProjectWrite prf) impossible
  uninhabited (ProjectRead prf) impossible

-- ## [ Negative Predicates ]

public export
data CanProjectNot : (how  : Project dir)
                  -> (type : Ty)
                  -> (u    : Usage type)
                          -> Type
  where
    ProjectWriteNot : (prf : IsFreeNot                type          ein)
                          -> CanProjectNot WRITE (TyChan type) (TyChan ein eout)

    ProjectReadNot : (prf : IsFreeNot                  type              eout)
                         -> CanProjectNot READ (TyChan type) (TyChan ein eout)

    ProjecNotPort : CanProjectNot how (TyPort ft) u
    ProjecNotGate : CanProjectNot how TyGate      u
    ProjecNotUnit : CanProjectNot how TyUnit      u

-- ## [ Decision Procedures ]

export
canProject : (how : Project dir)
          -> (u   : Usage type)
                 -> DecInfo (CanProjectNot how type u)
                            (CanProject    how type u)
canProject how (TyPort _)
  = No ProjecNotPort
       absurd

canProject WRITE (TyChan ein _) with (isFree ein)
  canProject WRITE (TyChan ein _) | (Yes prf)
    = Yes (ProjectWrite prf)

  canProject WRITE (TyChan ein _) | (No msg no)
    = No (ProjectWriteNot msg)
         (\(ProjectWrite prf) => no prf)

canProject READ (TyChan _ eout) with (isFree eout)
  canProject READ (TyChan _ eout) | (Yes prf)
    = Yes (ProjectRead prf)

  canProject READ (TyChan _ eout) | (No msg no)
    = No (ProjectReadNot msg)
         (\(ProjectRead prf) => no prf)

canProject how TyGate
  = No ProjecNotGate
       absurd

canProject how TyUnit
  = No ProjecNotUnit
       absurd

-- # [ Free Ports at a specific Index ]

-- ## [ Positive Predicates ]

public export
data CanProjectAt : (how  : Project dir)
                 -> (idx  : List Nat)
                 -> (type : Ty)
                 -> (u    : Usage type)
                         -> Type
  where
    ProjectAtWrite : (prf : IsFreeAt           idx         type          ein)
                         -> CanProjectAt WRITE idx (TyChan type) (TyChan ein eout)

    ProjectAtRead : (prf : IsFreeAt          idx         type              eout)
                        -> CanProjectAt READ idx (TyChan type) (TyChan ein eout)

Uninhabited (CanProjectAt how idx TyGate u) where
  uninhabited (ProjectAtWrite prf) impossible
  uninhabited (ProjectAtRead prf) impossible

Uninhabited (CanProjectAt how idx TyUnit u) where
  uninhabited (ProjectAtWrite prf) impossible
  uninhabited (ProjectAtRead prf) impossible

Uninhabited (CanProjectAt how idx (TyPort (f,dtype)) u) where
  uninhabited (ProjectAtWrite prf) impossible
  uninhabited (ProjectAtRead prf) impossible

-- ## [ Negative Predicates ]

public export
data CanProjectAtNot : (how  : Project dir)
                    -> (idx  : List Nat)
                    -> (type : Ty)
                    -> (u    : Usage type)
                            -> Type
  where
    ProjectAtWriteNot : (prf : IsFreeAtNot           idx         type          ein)
                            -> CanProjectAtNot WRITE idx (TyChan type) (TyChan ein eout)

    ProjectAtReadNot : (prf : IsFreeAtNot          idx         type              eout)
                           -> CanProjectAtNot READ idx (TyChan type) (TyChan ein eout)

    ProjecAtNotPort : CanProjectAtNot how idx (TyPort ft) u
    ProjecAtNotGate : CanProjectAtNot how idx TyGate      u
    ProjecAtNotUnit : CanProjectAtNot how idx TyUnit      u


-- ## [ Decision Procedures ]

export
canProjectAt : {type : Ty}
            -> (how : Project dir)
            -> (idx : List Nat)
            -> (u   : Usage type)
                   -> DecInfo (CanProjectAtNot how idx type u)
                              (CanProjectAt    how idx type u)
canProjectAt how idx (TyPort u)
  = No ProjecAtNotPort
       absurd

canProjectAt WRITE idx (TyChan ein _) with (isFreeAt idx ein)
  canProjectAt WRITE idx (TyChan ein _) | (Yes prf)
    = Yes (ProjectAtWrite prf)

  canProjectAt WRITE idx (TyChan ein _) | (No msg no)
    = No (ProjectAtWriteNot msg)
         (\(ProjectAtWrite prf) => no prf)

canProjectAt READ idx (TyChan _ eout) with (isFreeAt idx eout)
  canProjectAt READ idx (TyChan _ eout) | (Yes prf)
    = Yes (ProjectAtRead prf)

  canProjectAt READ idx (TyChan _ eout) | (No msg no)
    = No (ProjectAtReadNot msg)
         (\(ProjectAtRead prf) => no prf)

canProjectAt how idx TyGate
  = No ProjecAtNotGate
       absurd

canProjectAt how idx TyUnit
  = No ProjecAtNotUnit
       absurd

-- [ EOF ]
