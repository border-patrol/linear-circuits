|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Check.Lookup.ProjectAt

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List1
import Data.List.Elem
import Data.List.Quantifiers
import Data.DPair

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Views

import Toolkit.Data.Fin
import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.Whole
import Toolkit.Data.Location
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Toolkit.Data.List.AtIndex

import Toolkit.Data.DList.AtIndex

import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.NetList.Types
import Circuits.NetList.Linear.Core
import Circuits.NetList.Linear.Usage
import Circuits.NetList.Linear.Terms

import Circuits.NetList.Linear.Check.API

%default total

public export
CanProjectAt : {is   : List Item}
            -> (key  : String)
            -> (how  : Project dir)
            -> (idx  : List Nat)
            -> (ctxt : Context is)
                    -> Type
CanProjectAt str how idx ctxt
  = Exists Item (CanProjectAt how idx) str ctxt


canProjectAt' : {types : List Item}
             -> (how   : Project dir)
             -> (idx   : List Nat)
             -> (str   : String)
             -> (ctxt  : Context types)
                      -> DecInfo (Exists.Error (DPair Item (CanProjectAtNot how idx)))
                                 (CanProjectAt str how idx ctxt)
canProjectAt' how idx
    = exists (\i => transForm (Item.Channel.canProjectAt how idx i))
  where
    transForm : {i : _}
             -> DecInfo (CanProjectAtNot how idx i)
                        (CanProjectAt    how idx i)
            -> DecInfo (DPair Item (CanProjectAtNot how idx))
                                   (CanProjectAt    how idx i)
    transForm (Yes prfWhy) = Yes prfWhy
    transForm (No msgWhyNot prfWhyNot)
      = No (_ ** msgWhyNot) prfWhyNot


public export
data ProjectableChan : {types : List Item}
                    -> (how   : Project dir)
                    -> (idx   : List Nat)
                    -> (ctxt  : Context types)
                          -> Type
  where
    PC : {type : DType}
      -> {u    : Usage (TyChan (BVECT (W (S n) ItIsSucc) type))}
      -> {next : List Item}
      -> {ctxt : Context curr}
      -> (new  : Context next)
      -> (prf  : CanProjectAt how idx (I (TyChan (BVECT (W (S n) ItIsSucc)
                                                  type))
                                       u)
                                  curr)
      -> (use  : UseChannelAt    how idx curr prf next)
              -> ProjectableChan how idx ctxt

deBruijn : {ctxt : Context types}
        -> HoldsAtIndex Item Item (Holds Item (CanProjectAt how idx) str) ctxt loc
        -> AtIndex item types loc
        -> CanProjectAt how idx item types
deBruijn {ctxt = ((I str item) :: xs)} (Here (H prfK prf)) Here
  = Here Refl prf
deBruijn {ctxt = (x' :: xs)} (There contra x) (There later)
  = There (deBruijn x later)

update : {curr, next : List Item}
      -> {prf  : CanProjectAt how idx i curr}
      -> (ctxt : Context curr)
      -> (use  : UseChannelAt how idx curr prf next)
              -> Context next
update {curr = (i :: xs)} {next = (y :: xs)} ((I name i) :: rest) (UpdateHere use)
  = I name y :: rest
update {curr = (x :: xs)} {next = (x :: ys)} (elem :: y) (UpdateThere rest)
  = elem :: update y rest


export
canProjectAt : (fc    : FileContext)
            -> (how   : Project dir)
            -> {types : List Item}
            -> (idx   : List Nat)
            -> (str   : String)
            -> (ctxt  : Context types)
                     -> Linear (DPair Ty (Result types))
canProjectAt fc how idx str ctxt with (canProjectAt' how idx str ctxt)
  canProjectAt fc how idx str ctxt | (Yes (E (I (TyChan type) (TyChan ein eout)) item (ProjectAt prf) locC locN)) with (prf)
    canProjectAt fc WRITE idx str ctxt | (Yes (E (I (TyChan LOGIC) (TyChan ein eout)) item (ProjectAt prf) locC locN)) | (ProjectAtWrite x)
      = throwAt fc (ErrI "Internal error should not get here, this case is impossible.")

    canProjectAt fc WRITE idx str ctxt | (Yes (E (I (TyChan (BVECT (W (S n) ItIsSucc) type)) (TyChan ein eout)) item (ProjectAt prf) locC locN)) | (ProjectAtWrite x)
      = do let prfIdx = deBruijn locC locN
           let (new ** use) = useChannelAt _ prfIdx
           let next = update ctxt use
           R prfT <- embedAt fc (IOOB idx (BVECT (W (S n) ItIsSucc) type))
                                (hasTypeAt (BVECT (W (S n) ItIsSucc) type) idx)
           pure (_ ** R next (ProjectAt WRITE idx prfIdx use prfT))


    canProjectAt fc READ idx str ctxt | (Yes (E (I (TyChan LOGIC) (TyChan ein eout)) item (ProjectAt prf) locC locN)) | (ProjectAtRead x)
      = throwAt fc (ErrI "Internal error should not get here, this case is impossible.")

    canProjectAt fc READ idx str ctxt | (Yes (E (I (TyChan (BVECT (W (S n) ItIsSucc) type)) (TyChan ein eout)) item (ProjectAt prf) locC locN)) | (ProjectAtRead x)
      = do let prfIdx = deBruijn locC locN
           let (new ** use) = useChannelAt _ prfIdx
           let next = update ctxt use
           R prfT <- embedAt fc (IOOB idx (BVECT (W (S n) ItIsSucc) type))
                                (hasTypeAt (BVECT (W (S n) ItIsSucc) type) idx)
           pure (_ ** R next (ProjectAt READ idx prfIdx use prfT))

  canProjectAt fc how idx str ctxt | (No NotFound _)
    = throwAt fc (NotBound str)


  canProjectAt fc how idx str ctxt | (No (NotSatisfied ((I (TyPort x) _) ** prf)) _)
    = throwAt fc (ErrI "Internal error canProjectAt")
  canProjectAt fc how idx str ctxt | (No (NotSatisfied ((I (TyChan x) u) ** prf)) _)
    = throwAt fc (LinearityError ["\{str} := \{show u}"])

  canProjectAt fc how idx str ctxt | (No (NotSatisfied ((I _ _) ** prf)) _)
    = throwAt fc PortChanExpected

-- [ EOF ]
