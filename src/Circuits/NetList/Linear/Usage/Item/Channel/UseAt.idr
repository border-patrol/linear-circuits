||| Reason about useage of channel items.
|||
||| Module    : Channel.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.Item.Channel.UseAt

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String
import Data.Singleton

import Toolkit.Decidable.Informative
import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

import Circuits.NetList.Linear.Usage.DataType

import Circuits.NetList.Linear.Usage.DataType.Use.Full
import Circuits.NetList.Linear.Usage.DataType.Use.Partial

import Circuits.NetList.Linear.Usage.TermType
import Circuits.NetList.Linear.Context

import Circuits.NetList.Linear.Usage.TermType.Channel
import Circuits.NetList.Linear.Usage.TermType.Channel.Use

import Circuits.NetList.Linear.Usage.Item.Channel.CanProjectAt

%default total


public export
data UseAt : (how  : Project dir)
          -> (idx  : List Nat)
          -> (old  : Item)
          -> (prf  : CanProjectAt how idx old)
          -> (new  : Item)
          -> (prfN : Singleton new) -- A Hack to allow use of ElemSat
                  -> Type
  where
    UAt : (use : UseAt how idx    (TyChan type) (TyChan i o)             prf                   (TyChan i' o'))
              -> UseAt how idx (I (TyChan type) (TyChan i o)) (ProjectAt prf) (I (TyChan type) (TyChan i' o')) (Val (I (TyChan type) (TyChan i' o')))



public export
data Result : (how  : Project dir)
           -> (idx  : List Nat)
           -> (old  : Item)
           -> (prf  : CanProjectAt how idx old)
                   -> Type
  where
    R : {idx  : List Nat}
     -> {prf  : CanProjectAt how idx old}
     -> (new : Item)
     -> (use : UseAt  how idx old prf new (Val new))
            -> Result how idx old prf

export
useAt : {idx : List Nat}
     -> {old : Item}
     -> (prf : CanProjectAt how idx old)
            -> Result       how idx old prf
useAt (ProjectAt prf) with (useAt prf)
  useAt (ProjectAt prf) | (R new x) with (x) -- for coverage checker
    useAt (ProjectAt (ProjectAtWrite free)) | (R (TyChan newU eout) x) | (IsWriteAt y)
      = R (I _ (TyChan newU eout)) (UAt x)
    useAt (ProjectAt (ProjectAtRead free)) | (R (TyChan ein newU) x) | (IsReadAt y)
      = R (I _ (TyChan ein newU)) (UAt x)

-- [ EOF ]
