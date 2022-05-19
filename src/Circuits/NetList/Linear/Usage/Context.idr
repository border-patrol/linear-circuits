module Circuits.NetList.Linear.Usage.Context

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

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

import Circuits.NetList.Linear.Usage.DataType
import Circuits.NetList.Linear.Usage.DataType.Use.Full
import Circuits.NetList.Linear.Usage.DataType.Use.Partial

import Circuits.NetList.Linear.Usage.TermType
import Circuits.NetList.Linear.Usage.TermType.Use.Port
import Circuits.NetList.Linear.Usage.TermType.Use.Channel

import Circuits.NetList.Linear.Usage.Item

%default total

|||
|||
||| Construction of this will during type-checking...
public export
data IsFreePort : (item : Item)
               -> (ctxt : List Item)
                       -> Type
  where
    FreePortHere : (prf : IsFree        (TyPort (flow,dtype)) u)
                       -> IsFreePort (I (TyPort (flow,dtype)) u)
                                     (I (TyPort (flow,dtype)) u :: rest)

    FreePortThere : (later : IsFreePort (I (TyPort (flow,dtype)) u)              rest)
                          -> IsFreePort (I (TyPort (flow,dtype)) u) (not_item :: rest)

public export
data UsePort : (old : List Item)
            -> (prf : IsFreePort (I (TyPort (flow,dtype)) u) old)
            -> (new : List Item)
                   -> Type
  where
    UsePortHere : (use : Use        (TyPort (flow,dtype)) f                        pf  u pu)
                      -> UsePort (I (TyPort (flow,dtype)) f :: rest) (FreePortHere pf)
                                 (I (TyPort (flow,dtype)) u :: rest)

    UsePortThere : (later : UsePort          old                 rest           new)
                         -> UsePort (item :: old) (FreePortThere rest) (item :: new)

export
usePort : (old : List Item)
       -> (prf : IsFreePort (I (TyPort (flow,dtype)) u) old)
              -> DPair (List Item) (UsePort old prf)
usePort (I (TyPort (flow, dtype)) u :: rest) (FreePortHere prf) with (use prf)
  usePort (I (TyPort (flow, dtype)) u :: rest) (FreePortHere prf) | (R used prfU x)
    = MkDPair (I (TyPort (flow, dtype)) used :: rest) (UsePortHere x)

usePort (not_item :: rest) (FreePortThere later) with (usePort rest later)
  usePort (not_item :: rest) (FreePortThere later) | (MkDPair fst snd)
    = (not_item :: fst ** UsePortThere snd)


|||
|||
||| Construction of this will during type-checking...
public export
data IsFreeChannel : (how  : Project dir)
                  -> (item : Item)
                  -> (ctxt : List Item)
                          -> Type
  where
    FreeChannelHere : (prf : CanProject    how    (TyChan type) u)
                          -> IsFreeChannel how (I (TyChan type) u)
                                               (I (TyChan type) u  :: rest)

    FreeChannelThere : (later : IsFreeChannel how (I (TyChan type) u)              rest)
                             -> IsFreeChannel how (I (TyChan type) u) (not_item :: rest)

public export
data ProjectChannel : (how : Project dir)
                   -> (old : List Item)
                   -> (prf : IsFreeChannel how (I (TyChan dtype) u) old)
                   -> (new : List Item)
                          -> Type
  where
    ProjectHere : (use : Use            how    (TyChan type) o                           prf  n)
                      -> ProjectChannel how (I (TyChan type) o :: rest) (FreeChannelHere prf)
                                            (I (TyChan type) n :: rest)

    ProjectThere : (later : ProjectChannel how          old                    rest           new)
                         -> ProjectChannel how (item :: old) (FreeChannelThere rest) (item :: new)

export
projectChannel : (how : Project dir)
              -> (old : List Item)
              -> (prf : IsFreeChannel how (I (TyChan type) u) old)
                     -> DPair (List Item) (ProjectChannel how old prf)
projectChannel how (I (TyChan type) u :: rest) (FreeChannelHere prf) with (use prf)
  projectChannel how (I (TyChan type) u :: rest) (FreeChannelHere prf) | (R new x)
    = MkDPair (I (TyChan type) new :: rest) (ProjectHere x)

projectChannel how (not_item :: rest) (FreeChannelThere later) with (projectChannel how rest later)
  projectChannel how (not_item :: rest) (FreeChannelThere later) | (MkDPair fst snd)
    = MkDPair (not_item :: fst) (ProjectThere snd)


|||
|||
||| Construction of this will during type-checking...
public export
data CanIndexPort : (idx  : Fin n)
                 -> (item : Item)
                 -> (ctxt : List Item)
                         -> Type
  where
    CanIndexHere : (prf : IsFreeAt     idx    (TyPort (flow,dtype)) u)
                       -> CanIndexPort idx (I (TyPort (flow,dtype)) u)
                                           (I (TyPort (flow,dtype)) u  :: rest)

    CanIndexThere : (later : CanIndexPort idx (I (TyPort (flow,dtype)) u)              rest)
                          -> CanIndexPort idx (I (TyPort (flow,dtype)) u) (not_item :: rest)

public export
data IndexPort : (idx : Fin n)
              -> (old : List Item)
              -> (prf : CanIndexPort idx (I (TyPort (flow,dtype)) u) old)
              -> (new : List Item)
                     -> Type

  where
    IndexHere : (use : Use       idx    (TyPort (flow,type)) o                        prf  n pU)
                    -> IndexPort idx (I (TyPort (flow,type)) o :: rest) (CanIndexHere prf)
                                     (I (TyPort (flow,type)) n :: rest)

    IndexThere : (later : IndexPort idx          old                 rest           new)
                       -> IndexPort idx (item :: old) (CanIndexThere rest) (item :: new)

indexPort : (idx : Fin n)
         -> (old : List Item)
         -> (prf : CanIndexPort idx (I (TyPort (flow,dtype)) u) old)
                -> DPair (List Item) (IndexPort idx old prf)

indexPort idx (I (TyPort (flow, dtype)) u :: rest) (CanIndexHere prf) with (use idx prf)
  indexPort idx (I (TyPort (flow, dtype)) u :: rest) (CanIndexHere prf) | (R used prfU holds)
    = MkDPair (I (TyPort (flow, dtype)) used :: rest) (IndexHere holds)


indexPort idx (not_item :: rest) (CanIndexThere later) with (indexPort idx rest later)
  indexPort idx (not_item :: rest) (CanIndexThere later) | (MkDPair fst snd)
    = MkDPair (not_item :: fst) (IndexThere snd)


-- [ EOF ]
