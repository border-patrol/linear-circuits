|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Check.Stop

import Decidable.Equality

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
import Toolkit.Data.List.Subset

import Toolkit.Data.DList.AtIndex

import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.NetList.Types
import Circuits.NetList.Linear.Core
import Circuits.NetList.Linear.Usage

import Circuits.NetList.Linear.Check.API

%default total

canStop' : {x : Item}
       -> (i : Item x)
            -> DecInfo (CanStopNot x)
                       (CanStop    x)
canStop' (I name x) with (canStop x)
  canStop' (I name x) | (Yes prf)
    = Yes prf

  canStop' (I name x) | (No msg no)
    = No msg no

public export
data Examine : List Item -> Type where
  AUN : Interleaving   freeish used ctxt
     -> All CanStopNot freeish
     -> All CanStop            used
     -> Context        freeish
     -> Context                used
     -> Examine                     ctxt

examine : {types : List Item}
       -> (ctxt  : Context types)
                -> Examine types
examine []
  = AUN [] [] [] [] []

examine (x :: xs) with (canStop' x)
  examine (x :: xs) | rX with (examine xs)
    examine (x :: xs) | (Yes prf) | (AUN is fs us cf cu)
      = AUN (Right is) fs (prf :: us) cf (x::cu)
    examine (x :: xs) | (No mX no) | (AUN is fs us cf cu)
      = AUN (Left is) (mX :: fs) us (x :: cf) cu

data Analysis : (res : Examine types) -> Type where
  AllOk    : Analysis (AUN is Nil xs Nil ys)
  AllOkNot : Analysis (AUN is ps xs ns ys)

analysis : (res : Examine types) -> Analysis res
analysis (AUN is [] us [] pu)
  = AllOk
analysis (AUN is (x :: y) us pf pu)
  = AllOkNot


eek : Interleaving Nil xs ys -> xs = ys
eek [] = Refl
eek (Right x) with (eek x)
  eek (Right x) | Refl = Refl

export
canStop : {types : List Item}
       -> (fc    : FileContext)
       -> (ctxt  : Context types)
                -> Linear (All CanStop types)
canStop fc ctxt with (examine ctxt)
  canStop fc ctxt | res with (analysis res)
    canStop fc ctxt | (AUN is [] xs [] ys) | AllOk with (eek is)
      canStop fc ctxt | (AUN is [] xs [] ys) | AllOk | Refl
        = pure xs
    canStop fc ctxt | (AUN is ps xs ns ys) | AllOkNot
      = throwAt fc  (LinearityError (mapToList (\(I n (I ty u)) => "\{n} := \{show u}") ns))

-- [ EOF ]
