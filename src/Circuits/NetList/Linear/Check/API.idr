|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Check.API

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List.Elem
import Data.List.Quantifiers
import Data.Fin

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Views

import Toolkit.Data.Whole
import Toolkit.Data.Location

import Toolkit.Data.DList
import Toolkit.Data.List.AtIndex

import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.NetList.Types

import Circuits.NetList.Linear.Core

import Circuits.NetList.Linear.Usage
import Circuits.NetList.Linear.Terms

%default total

-- # [ API ]

export
throw : Check.Error -> Linear a
throw = (throw . Linear.TyCheck)

export
throwAt : FileContext
       -> Check.Error
       -> Linear a
throwAt fc = (API.throw . Err fc)

export
embedAt : FileContext
       -> (e -> Check.Error)
       -> Either e a
       -> Linear   a
embedAt _ _ (Right prf)
  = pure prf
embedAt fc f (Left err)
  = throwAt fc (f err)

namespace Decidable
  export
  embedAt : FileContext
         -> Check.Error
         -> Dec     a
         -> Linear a
  embedAt _ _ (Yes prf)
    = pure prf
  embedAt fc err (No _)
    = throwAt fc err

  namespace Informative
    export
    embedAt : FileContext
           -> Check.Error
           -> DecInfo e a
           -> Linear   a
    embedAt _ _ (Yes prfWhy)
      = pure prfWhy
    embedAt fc err (No _ _)
      = throwAt fc err

    export
    embedAtInfo : FileContext
               -> Check.Error
               -> DecInfo e a
               -> Linear   a
    embedAtInfo = embedAt

-- # [ Typing Context/Environment ]

public export
Context : List Item -> Type
Context = Context Item

-- # [ Containing results ]

public export
data Result : (curr : List Item)
           -> (ty   : Ty)
           -> Type
  where
    R : {cout : _}
     -> {type : Ty}
     -> (new  : Context cout)
     -> (term : Term cin type cout)
             -> Result cin type

-- [ EOF ]
