module Circuits.NetList.Linear.Check.Lookup.PortAt

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
FreePortAt : {is   : List Item}
          -> (key  : String)
          -> (idx  : List Nat)
          -> (ctxt : Context is)
                  -> Type
FreePortAt str idx ctxt
  = Exists Item (IsFreeAt idx) str ctxt


isFreePortAt' : {types : List Item}
           -> (idx   : List Nat)
           -> (str   : String)
           -> (ctxt  : Context types)
                    -> DecInfo (Exists.Error (DPair Item (IsFreeAtNot idx)))
                               (FreePortAt str idx ctxt)
isFreePortAt' idx
    = exists (\i => transForm (Item.Port.isFreeAt idx i))
  where
    transForm : {i : _} -> DecInfo (IsFreeAtNot idx i)          (IsFreeAt idx i)
                        -> DecInfo (DPair Item (IsFreeAtNot idx)) (IsFreeAt idx i)
    transForm (Yes prfWhy) = Yes prfWhy
    transForm (No msgWhyNot prfWhyNot)
      = No (_ ** msgWhyNot) prfWhyNot

public export
data FreeUsedPort : {types : List Item}
                 -> (idx   : List Nat)
                 -> (ctxt  : Context types)
                          -> Type
  where
    FUP : {flow : Direction}
       -> {type : DType}
       -> {u    : Usage (TyPort (flow, BVECT (W (S n) ItIsSucc) type))}
       -> {next : List Item}
       -> {ctxt : Context curr}
       -> (new  : Context next)
       -> (idir : Index flow)
       -> (prf  : IsFreePortAt idx (I (TyPort (flow, BVECT (W (S n) ItIsSucc)
                                                           type))
                                       u)
                                   curr)
       -> (use  : UsePortAt    idx curr prf next)
               -> FreeUsedPort idx ctxt

deBruijn : {ctxt : Context types}
        -> HoldsAtIndex Item Item (Holds Item (IsFreeAt idx) str) ctxt loc
        -> AtIndex item types loc
        -> IsFreePortAt idx item types
deBruijn {ctxt = ((I str item) :: xs)} (Here (H prfK prf)) Here
  = Here Refl prf
deBruijn {ctxt = (x' :: xs)} (There contra x) (There later)
  = There (deBruijn x later)

update : {curr, next : List Item}
      -> {prf  : IsFreePortAt idx i curr}
      -> (ctxt : Context curr)
      -> (use  : UsePortAt idx curr prf next)
              -> Context next
update {curr = (i :: xs)} {next = (y :: xs)} ((I name i) :: rest) (UpdateHere use)
  = I name y :: rest
update {curr = (x :: xs)} {next = (x :: ys)} (elem :: y) (UpdateThere rest)
  = elem :: update y rest

export
isFreePortAt : (fc    : FileContext)
            -> {types : List Item}
            -> (idx   : List Nat)
            -> (str   : String)
            -> (ctxt  : Context types)
                     -> Linear (DPair Ty (Result types))
isFreePortAt fc idx str ctxt with (isFreePortAt' idx str ctxt)
  isFreePortAt fc str idx ctxt | (Yes (E (I type u) item (FreeAt prf) locC locN)) with (prf)
    isFreePortAt fc str idx ctxt | (Yes (E (I (TyPort (flow, BVECT (W (S n) ItIsSucc) type)) (TyPort us)) item (FreeAt prf) locC locN)) | (FreeAt x)

      = do let prfIdx = deBruijn locC locN
           let (new ** use) = usePortAt _ prfIdx
           let next = update ctxt use
           let idir = case flow of
                        INPUT => DOWN DI
                        OUTPUT => UP UO
                        INOUT => UP UB
           R prfT <- embedAt fc (IOOB str (BVECT (W (S n) ItIsSucc) type))
                                (hasTypeAt (BVECT (W (S n) ItIsSucc) type) str)
           pure (_ ** R next (Index idir str prfIdx use prfT))


  isFreePortAt fc idx str ctxt | (No msg _) with (msg)
    isFreePortAt fc idx str ctxt | (No msg _) | NotFound
      = throwAt fc (NotBound str)
    isFreePortAt fc idx str ctxt | (No msg _) | (NotSatisfied (((I (TyPort (flow, type)) (TyPort u)) ** (FreeAtNot (FreeAtNot prf)))))
      = throwAt fc (LinearityError ["\{str} := \{show u}"])
    isFreePortAt fc idx str ctxt | (No msg _) | (NotSatisfied (((I (TyChan type) u) ** (FreeAtNot FreeAtNotChan))))
      = throwAt fc PortExpected
    isFreePortAt fc idx str ctxt | (No msg _) | (NotSatisfied (((I TyGate u) ** (FreeAtNot FreeAtNotGate))))
      = throwAt fc PortChanExpected
    isFreePortAt fc idx str ctxt | (No msg _) | (NotSatisfied (((I TyUnit u) ** (FreeAtNot FreeAtNotUnit))))
      = throwAt fc PortChanExpected

-- [ EOF ]
