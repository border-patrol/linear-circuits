module Circuits.Idealised.Check

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
import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming


import Circuits.Split
import Circuits.Idealised.Core
import Circuits.Idealised.Types
import Circuits.Idealised.Terms
import Circuits.Idealised.AST


%default total

public export
Context : List (Ty, Usage) -> Type
Context = Context (Ty,Usage)

namespace FreeVar

  public export
  data IsFree : (item : (Ty, Usage)) -> Type
    where
      FVar : (prf : u = FREE)
                 -> IsFree (type, u)


  Uninhabited (IsFree (ty,USED)) where
    uninhabited (FVar Refl) impossible

  isFree : (item : (Ty, Usage))
                -> DecInfo ()
                           (IsFree item)
  isFree (ty, USED)
    = No () absurd

  isFree (ty, FREE)
    = Yes (FVar Refl)

  public export
  FreeVar : {types : List (Ty, Usage)}
         -> (key   : String)
         -> (ctxt  : Context types)
                  -> Type
  FreeVar str ctxt
   = Exists (Ty,Usage)
            IsFree
            str
            ctxt

  export
  lookup : {types : List (Ty, Usage)}
        -> (str  : String)
        -> (ctxt : Context types)
                -> DecInfo (Exists.Error ())
                           (FreeVar str ctxt)
  lookup = exists isFree


use : (ctxt : Context curr)
   -> (use  : Use curr prf next)
           -> Context next
use (I k (ty,FREE) :: rest) H
  = I k (ty, USED) :: rest

use (head :: tail) (T later)
  = head :: use tail later


isUsed : (ctxt : Context types)
              -> Dec (All Used types)
isUsed []
  = Yes []

isUsed ((I name x) :: tail) with (used x)
  isUsed ((I name x) :: tail) | (Yes pH) with (isUsed tail)
    isUsed ((I name x) :: tail) | (Yes pH) | (Yes pT)
      = Yes (pH :: pT)

    isUsed ((I name x) :: tail) | (Yes pH) | (No contra)
      = No (\(a::as) => contra as)

  isUsed ((I name x) :: tail) | (No contra)
    = No (\(a::as) => contra a)

withLocThrow : FileContext -> Check.Error -> Idealised a
withLocThrow fc e = throw (TyCheck $ Err fc e)

throw : Check.Error -> Idealised a
throw = (throw . TyCheck)

public export
allEqual : FileContext
        -> (a,b,c : DType)
                 -> Idealised (AllEqual a b c)
allEqual fc a b c with (Views.allEqual a b c)
  allEqual fc c c c | (Yes AE)
    = pure AE
  allEqual fc a b c | (No AB prfWhyNot)
    = withLocThrow fc (MismatchGate a b)
  allEqual fc a b c | (No AC prfWhyNot)
    = withLocThrow fc (MismatchGate a c)


data Result : (curr : List (Ty,Usage))
           -> Type
  where
    R : {cout : _}
     -> (type : Ty)
     -> (new  : Context cout)
     -> (term : Term cin type cout)
             -> Result cin

check : {cin  : List (Ty,Usage)}
     -> (curr : Context cin)
     -> (ast  : AST)
             -> Idealised (Result cin)

check curr (Var x) with (lookup (get x) curr)
  check curr (Var x) | (Yes (E type item prf locC locN)) with (prf)
    check curr (Var x) | (Yes (E (type, u) item prf locC locN)) | (FVar prf1) with (prf1)
      check curr (Var x) | (Yes (E (type, FREE) item prf locC locN)) | (FVar prf1) | Refl with (use (V _ locN))
        check curr (Var x) | (Yes (E (type, FREE) item prf locC locN)) | (FVar prf1) | Refl | (MkDPair next pU) with (use curr pU)
          check curr (Var x) | (Yes (E (type, FREE) item prf locC locN)) | (FVar prf1) | Refl | (MkDPair next pU) | new
            = pure (R type new (Var (V _ locN) pU))

  check curr (Var x) | (No msg _)
    = withLocThrow (span x) (ElemFail (get x) msg)

check curr (Input fc x y name body)

  = do R TyUnit Nil body <- check (I (get name) ((TyPort (MkPair x y)),FREE) :: curr)
                                    body
           | R ty Nil _ => throw (Mismatch TyUnit ty)
           | R _  xs  _ => withLocThrow fc (LinearityError xs)

       pure (R TyUnit Nil (NewSignal x y body))

check curr (Wire fc type a b body)

  = do R TyUnit Nil term <- check (I (get a) ((TyPort (MkPair OUTPUT type)), FREE) ::
                                   I (get b) ((TyPort (MkPair INPUT  type)), FREE) :: curr)
                                  body
           | R ty Nil _ => throw (Mismatch TyUnit ty)
           | R ty xs  _ => withLocThrow fc (LinearityError xs)

       pure (R TyUnit Nil (Wire type term))

check curr (Seq x y)
  = do R TyGate ex x <- check curr x
         | R ty _ _ => throw (Mismatch TyGate ty)

       R TyUnit Nil y <- check ex y
         | R ty Nil _ => throw (Mismatch TyUnit ty)
         | R ty xs  _ => throw (LinearityError xs)

       pure (R TyUnit Nil (Seq x y))

check curr (Mux fc o c a b)
  = do R (TyPort (OUTPUT,dtypeA)) cO o <- check curr o
         | _ => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT,LOGIC)) cC c <- check cO c
         | R ty _ _ => withLocThrow fc (Mismatch (TyPort (INPUT,LOGIC)) ty)

       R (TyPort (INPUT,dtypeB)) cA a <- check cC a
         | _ => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT,dtypeC)) cB b <- check cA b
         | _ => withLocThrow fc (PortExpected OUTPUT)


       AE <- allEqual fc dtypeA dtypeB dtypeC

       pure (R TyGate cB (Mux o c a b))

check curr (Dup fc a b i)
  = do R (TyPort (OUTPUT,dtypeA)) cA a <- check curr a
         | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (OUTPUT,dtypeB)) cB b <- check cA b
         | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT,dtypeC)) cI i <- check cB i
         | ty => withLocThrow fc (PortExpected INPUT)

       AE <- allEqual fc dtypeA dtypeB dtypeC

       pure (R TyGate cI (Dup a b i))

check curr (Not fc a b)
  = do R (TyPort (OUTPUT,LOGIC)) cA a <- check curr a
         | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT,LOGIC)) cB b <- check cA b
         | ty => withLocThrow fc (PortExpected INPUT)

       pure (R TyGate cB (Not a b))

check curr (Gate fc k a b c)
  = do R (TyPort (OUTPUT,LOGIC)) cA a <- check curr a
         | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT,LOGIC)) cB b <- check cA b
         | ty => withLocThrow fc (PortExpected INPUT)

       R (TyPort (INPUT,LOGIC)) cC c <- check cB c
         | ty => withLocThrow fc (PortExpected INPUT)


       pure (R TyGate cC (Gate k a b c))


check curr (IndexS fc o i)
  = do R (TyPort (OUTPUT,dtypeO)) cO termO <- check curr o
         | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT,BVECT (W (S Z) ItIsSucc) dtypeI)) cI termI <- check cO i
         | R (TyPort (INPUT, BVECT s type)) _ _
             => withLocThrow fc (Mismatch (TyPort (INPUT, BVECT (W (S Z) ItIsSucc) type))
                                          (TyPort (INPUT, BVECT s type)))
         | ty => withLocThrow fc (PortExpected INPUT)

       Refl <- embed (TyCheck $ Err fc (MismatchGate dtypeO  dtypeI))
                     (decEq dtypeO dtypeI)


       pure (R TyGate cI (IndexSingleton termO termI))

check curr (IndexE fc k a b i)

  = do R (TyPort (OUTPUT,dtypeA)) cA termA <- check curr a
                  | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (OUTPUT,BVECT free dtypeB)) cB termB <- check cA b
                  | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT,BVECT size dtypeC)) cI termI <- check cB i
                  | ty => withLocThrow fc (PortExpected INPUT)

       AE <- allEqual fc dtypeA dtypeB dtypeC

       let p = case k of { F => minus (toNat size) 1; L => 0}

       (s ** prf) <- embed (const $ TyCheck $ Err fc (NotEdgeCase (InvalidEdge (toNat size) (S Z) (toNat free))))
                           (EdgeCase.index size p)


       Refl <- embed (TyCheck $ Err fc (NotEdgeCase (InvalidEdge (toNat size) (S Z) (toNat free))))
                     (decEq free s)


       pure (R TyGate cI (IndexEdge p prf termA termB termI))

check curr (IndexP fc p a b c i)
  = do R (TyPort (OUTPUT,dtypeA)) cA termA <- check curr a
                  | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (OUTPUT,BVECT freeB dtypeB)) cB termB <- check cA b
                  | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (OUTPUT,BVECT freeC dtypeC)) cC termC <- check cB c
                  | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT,BVECT size dtypeD)) cI termI <- check cC i
                  | ty => withLocThrow fc (PortExpected INPUT)

       Refl <- embed (TyCheck $ Err fc (MismatchGate dtypeA (BVECT freeB dtypeB)))
                     (decEq dtypeA dtypeB)

       Refl <- embed (TyCheck $ Err fc (MismatchGate (BVECT freeB dtypeB) (BVECT freeC dtypeC)))
                     (decEq dtypeB dtypeC)


       Refl <- embed (TyCheck $ Err fc (MismatchGate (BVECT freeC dtypeC) (BVECT size dtypeD)))
                     (decEq dtypeC dtypeD)


       (a ** b ** prf) <- embed (const $ TyCheck $ Err fc (NotEdgeCase (InvalidSplit p (toNat size) (toNat freeB) (toNat freeC))))
                                (Pivot.index p size)


       Refl <- embed (TyCheck $ Err fc (MismatchGate (BVECT a     dtypeB)
                                                     (BVECT freeB dtypeB)))
                     (decEq freeB a)

       Refl <- embed (TyCheck $ Err fc (MismatchGate (BVECT b     dtypeB)
                                                     (BVECT freeC dtypeB)))
                     (decEq freeC b)

       pure (R TyGate cI (IndexSplit p prf termA termB termC termI))

check curr (MergeS fc o i)

  = do R (TyPort (OUTPUT,BVECT (W (S Z) ItIsSucc) dtypeO)) cO termO <- check curr o
           | R (TyPort (INPUT, BVECT s type)) _ _
                => withLocThrow fc (Mismatch (TyPort (OUTPUT, BVECT (W (S Z) ItIsSucc) type))
                                             (TyPort (INPUT,  BVECT s                  type)))
           | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT, dtypeI)) cI termI <- check cO i
           | ty => withLocThrow fc (PortExpected INPUT)

       Refl <- embed (TyCheck $ Err fc (MismatchGate dtypeO dtypeI))
                     (decEq dtypeO dtypeI)


       pure (R TyGate cI (MergeSingleton termO termI))


check curr (MergeV fc o a b)

  = do R (TyPort (OUTPUT, dtypeO)) cO termO <- check curr o
           | ty => withLocThrow fc (PortExpected OUTPUT)

       R (TyPort (INPUT, dtypeA)) cA termA <- check cO a
           | ty => withLocThrow fc (PortExpected INPUT)

       R (TyPort (INPUT, dtypeB)) cB termB <- check cA b
           | ty => withLocThrow fc (PortExpected INPUT)

       case Views.allEqual LOGIC dtypeA dtypeB of
         Yes AE
           => do Refl <- embed (TyCheck (Err fc (MismatchGate (BVECT (W (S (S Z)) ItIsSucc) LOGIC)
                                                              dtypeO)))
                               (decEq dtypeO (BVECT (W (S (S Z)) ItIsSucc) LOGIC))

                 pure (R TyGate cB (Merge2L2V termO termA termB))
         No msg prf
           => case dtypeO of
                LOGIC => withLocThrow fc VectorExpected
                BVECT sO tO
                  => case dtypeA of
                       LOGIC => withLocThrow fc VectorExpected
                       BVECT sA tA
                         => case dtypeB of
                              LOGIC => withLocThrow fc VectorExpected
                              BVECT sB tB
                                => do prfS <- embed (TyCheck (Err fc (VectorSizeMismatch sO sA sB)))
                                                    (isPlus sA sB sO)

                                      AE <- allEqual fc tO tA tB

                                      pure (R TyGate cB (Merge2V2V prfS termO termA termB))


check curr (Stop fc)
  = do prf <- embed (TyCheck (Err fc (LinearityError curr)))
                    (isUsed curr)

       pure (R TyUnit Nil (Stop prf))

namespace Design

  export
  check : (ast : AST)
              -> Idealised (Term Nil TyUnit Nil)
  check ast
    = do R TyUnit Nil term <- check Nil ast
           | R ty _ _ => throw (TyCheck (Mismatch TyUnit ty))
         pure term

-- [ EOF ]
