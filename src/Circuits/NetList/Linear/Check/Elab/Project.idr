|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Check.Elab.Project

import Decidable.Equality
import Data.Singleton
import Data.Nat
import Data.String
import Data.List.Elem
import Data.List.Quantifiers
import Data.DPair

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Views

import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Whole
import Toolkit.Data.Location
import Toolkit.Data.DList

import Toolkit.Data.List.AtIndex

import Toolkit.Data.DList.AtIndex

import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.NetList.Types
import Circuits.NetList.Linear.Core
import Circuits.NetList.Linear.Usage
import Circuits.NetList.Linear.Terms

import Circuits.NetList.Linear.Check.API

%default total

||| Sadly conversion of Existential quantifiers between lists is not decidable; lists are not sets and the element might be satisfied later in the list...
|||
||| Until I can find a way to do the Decidable conversion, let us keep it as either.
export
canProject : {types : List Item }
          -> (how   : Project dir)
          -> (prf   : IsChan                    (I (TyChan type) (TyChan uin uout)) types)
                   -> Either (CanProjectNot how (I (TyChan type) (TyChan uin uout)) types)
                             (CanProject    how (I (TyChan type) (TyChan uin uout)) types)

canProject how (Here Refl (IC (Val (I (TyChan type) (TyChan uin uout))))) {types = ((I (TyChan type) (TyChan uin uout)) :: xs)} with (canProject how (I (TyChan type) (TyChan uin uout)))
  canProject how (Here Refl (IC (Val (I (TyChan type) (TyChan uin uout))))) {types = ((I (TyChan type) (TyChan uin uout)) :: xs)} | (Yes prf)
    = Right (Here Refl prf)
  canProject how (Here Refl (IC (Val (I (TyChan type) (TyChan uin uout))))) {types = ((I (TyChan type) (TyChan uin uout)) :: xs)} | (No msg no)
    = Left (Here Refl msg)

canProject how (There rest) {types = (y :: xs)} with (canProject how rest)
  canProject how (There rest) {types = (y :: xs)} | (Left x)
    = Left (There x)
  canProject how (There rest) {types = (y :: xs)} | (Right x)
    = Right (There x)

export
update : {curr, next : List Item}
      -> {prf  : CanProject how item curr}
      -> (ctxt : Context curr)
      -> (use  : UseChannel how curr prf next)
              -> Context next
update {curr = (i :: xs)} {next = (y :: xs)} ((I name i) :: rest) (UpdateHere use)
  = I name y :: rest
update {curr = (x :: xs)} {next = (x :: ys)} (h :: t) (UpdateThere rest)
  = h :: update t rest

-- [ EOF ]
