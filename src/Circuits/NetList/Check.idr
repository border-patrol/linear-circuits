|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Check

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List.Elem
import Data.List.Quantifiers
import Data.Fin
import Data.Singleton

import Toolkit.Decidable.Informative

import Toolkit.Data.Location
import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.DeBruijn.Context

import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

import Circuits.NetList.Core
import Circuits.NetList.Types
import Circuits.NetList.Terms
import Circuits.NetList.AST

%default total

public export
Context : List Ty -> Type
Context = Context Ty

throw : Check.Error -> NetList a
throw = (throw . TyCheck)

throwAt : FileContext
       -> Check.Error
       -> NetList a
throwAt fc = (Check.throw . Err fc)

embedAt : FileContext
       -> Check.Error
       -> Dec     a
       -> NetList a
embedAt _ _ (Yes prf)
  = pure prf
embedAt fc err (No _)
  = throwAt fc err

embedAtInfo : FileContext
           -> Check.Error
           -> DecInfo e a
           -> NetList   a
embedAtInfo _ _ (Yes prfWhy)
  = pure prfWhy
embedAtInfo fc err (No _ _)
  = throwAt fc err

||| Naive program transformations and checks.
namespace Elab

  export
  getDataType : (fc   : FileContext)
             -> (term : (type ** Term ctxt type))
                     -> NetList DType
  getDataType fc (MkDPair (TyPort (d,x)) snd)
    = pure x
  getDataType fc (MkDPair (TyChan x) snd)
    = pure x
  getDataType fc (MkDPair type snd)
    = throwAt fc PortChanExpected



  ||| Need to make sure that the indices are in the correct direction.
  rewriteTerm : Cast flow expected
             -> Index INOUT
             -> Term ctxt (TyPort (flow,type))
             -> Term ctxt (TyPort (flow,type))
  rewriteTerm c d (Var prf) = Var prf

  rewriteTerm BI (UP UB) (Index idir what idx)
    = Index (UP UB) (rewriteTerm BI (UP UB) what) idx

  rewriteTerm BI (DOWN DB) (Index idir what idx)
    = Index (DOWN DB) (rewriteTerm BI (DOWN DB) what) idx

  rewriteTerm BO (UP UB) (Index idir what idx)
    = Index (UP UB) (rewriteTerm BI (UP UB) what) idx

  rewriteTerm BO (DOWN DB) (Index idir what idx)
    = Index (DOWN DB) (rewriteTerm BI (DOWN DB) what) idx

  rewriteTerm BI _ (Project WRITE _) impossible
  rewriteTerm BO _ (Project WRITE _) impossible
  rewriteTerm BI _ (Project READ _) impossible
  rewriteTerm BO _ (Project READ _) impossible

  rewriteTerm BI _ (Cast BI _) impossible
  rewriteTerm BO _ (Cast BI _) impossible
  rewriteTerm BI _ (Cast BO _) impossible
  rewriteTerm BO _ (Cast BO _) impossible

  ||| When casting we finally know which direction indexing should go,
  ||| so lets fix that.
  shouldCast : {type : DType}
            -> (flow,expected : Direction)
            -> (term : Term ctxt (TyPort (flow,type)))
                    -> Dec ( Cast flow expected
                           , Term ctxt (TyPort (expected,type))
                           )
  shouldCast flow expected term with (Cast.cast flow expected)
    shouldCast INOUT INPUT term | (Yes BI) with (dirFromCast BI)
      shouldCast INOUT INPUT term | (Yes BI) | idir
        = Yes $ MkPair BI (Cast BI (rewriteTerm BI idir term))


    shouldCast INOUT OUTPUT term | (Yes BO) with (dirFromCast BO)
      shouldCast INOUT OUTPUT term | (Yes BO) | idir
        = Yes $ MkPair BO (Cast BO (rewriteTerm BO idir term))

    shouldCast flow expected term | (No contra)
      = No (\(prf,t) => contra prf)

  portCast : {type     : DType}
          -> {flow     : Direction}
          -> (fc       : FileContext)
          -> (expected : Direction)
          -> (term     : Term ctxt (TyPort (flow,type)))
                      -> NetList (Term ctxt (TyPort (expected,type)))

  portCast {type} {flow = flow} fc exp term with (shouldCast flow exp term)
    portCast {type} {flow = flow} fc exp term | Yes (p,e)
      = pure e
    portCast {type} {flow = flow} fc exp term | No contra with (decEq flow exp)
      portCast {type} {flow = exp} fc exp term | No contra | (Yes Refl)
        = pure term
      portCast {type} {flow = flow} fc exp term | No contra | (No f)
        = throwAt fc (Mismatch (TyPort (exp,type))
                               (TyPort (flow,type)))

  export
  checkPort : (fc    : FileContext)
           -> (exdir : Direction)
           -> (expty : DType)
           -> (term  : (type ** Term ctxt type))
                    -> NetList (Term ctxt (TyPort (exdir,expty)))

  -- [ NOTE ]
  --
  checkPort fc exdir exty (MkDPair (TyPort (given,x)) term)
    = do Refl <- embedAt fc
                         (MismatchD exty x)
                         (decEq exty x)


         portCast fc exdir term

  -- [ NOTE ]
  --
  -- READ implies INPUT
  checkPort fc INPUT exty (MkDPair (TyChan x) term)
    = do Refl <- embedAt fc (MismatchD exty x)
                            (decEq exty x)


         pure (Project READ term)

  -- [ NOTE ]
  --
  -- WRITE implies OUTPUT
  checkPort fc OUTPUT exty (MkDPair (TyChan x) term)
    = do Refl <- embedAt fc (MismatchD exty x)
                            (decEq exty x)


         pure (Project WRITE term)

  -- [ NOTE ]
  --
  -- INOUT Chan's impossible.
  checkPort fc INOUT exty (MkDPair (TyChan x) term)
     = throwAt fc (ErrI "INOUT CHAN not expected")


  -- [ NOTE ]
  --
  -- Gates/TyUnit not expected
  checkPort fc exdir exty (MkDPair type term)
     = throwAt fc (Mismatch (TyPort (exdir,exty))
                            type)

  export
  indexDir : {flow : Direction}
          -> (fc   : FileContext)
          -> (term : Term ctxt (TyPort (flow,BVECT (W (S n) ItIsSucc) type)))
                  -> NetList (Index flow)
  indexDir {flow} fc term with (flow)
    indexDir {flow = flow} fc term | INPUT
      = pure (DOWN DI)
    indexDir {flow = flow} fc term | OUTPUT
      = pure (UP UO)
    indexDir {flow = flow} fc (Var prf) | INOUT
      = pure (UP UB)
    indexDir {flow = flow} fc (Index idir what idx) | INOUT
      = pure idir
    indexDir {flow = flow} fc (Project how what) | INOUT
      = throwAt fc (ErrI "Shouldn't happen impossible indexing a projection with inout")
    indexDir {flow = flow} fc (Cast x what) | INOUT
      = throwAt fc (ErrI "Shouldn't happen impossible indexing a cast with inout")

construct : {types : List Ty}
         -> (curr : Context types)
         -> (ast  : AST)
                 -> NetList (DPair Ty (Term types))

construct curr (Var x)
  = do prf <- embedAtInfo (span x)
                          (NotBound (get x))
                          (lookup (get x) curr)

       let (ty ** loc ** idx) = deBruijn prf

       pure (ty ** Var (V loc idx))

construct curr (Port fc flow ty n body)
  = do (TyUnit ** term) <- construct (extend curr (get n) (TyPort (flow, ty)))
                                     body
         | (ty ** _) => throwAt fc (Mismatch TyUnit ty)

       pure (_ ** Port flow ty term)

construct curr (Wire fc ty n body)

  = do (TyUnit ** term) <- construct (extend curr (get n) (TyChan ty))
                                     body
         | (ty ** _) => throwAt fc (Mismatch TyUnit ty)

       pure (_ ** Wire ty term)

construct curr (GateDecl fc n g body)
  = do (TyGate ** gate) <- construct curr g
         | (type ** _) => throwAt fc (Mismatch TyGate type)

       (TyUnit ** term) <- construct (extend curr (get n) TyGate)
                                     body
         | (type ** _) => throwAt fc (Mismatch TyUnit type)

       pure (_ ** GateDecl gate term)

construct curr (Shim fc dir thing)
  = do t <- construct curr thing

       dtype <- getDataType fc t

       term <- checkPort fc dir dtype t

       pure (_ ** term)


construct curr (Assign fc o i rest)
  =  do termI <- construct curr i

        ity <- getDataType fc termI

        termO <- construct curr o

        oty <- getDataType fc termO

        Refl <- embedAt fc (MismatchD ity oty)
                           (decEq ity oty)

        o' <- checkPort fc OUTPUT ity termO

        i' <- checkPort fc INPUT  ity termI

        (TyUnit ** r') <- construct curr rest
          | (type ** _) => throwAt fc (Mismatch TyUnit type)

        pure (_ ** Assign o' i' r')

construct curr (Mux fc o c l r)
  = do termO <- construct curr o
       termC <- construct curr c
       termL <- construct curr l
       termR <- construct curr r

       o' <- checkPort fc OUTPUT LOGIC termO
       c' <- checkPort fc INPUT  LOGIC termC
       l' <- checkPort fc INPUT  LOGIC termL
       r' <- checkPort fc INPUT  LOGIC termR

       pure (_ ** Mux o' c' l' r')

construct curr (GateU fc k o i)

  = do termO <- construct curr o
       termI <- construct curr i

       o' <- checkPort fc OUTPUT LOGIC termO
       i' <- checkPort fc INPUT  LOGIC termI

       pure (_ ** GateU k o' i')

construct curr (GateB fc k o l r)

  = do termO <- construct curr o
       termL <- construct curr l
       termR <- construct curr r

       o' <- checkPort fc OUTPUT LOGIC termO
       l' <- checkPort fc INPUT  LOGIC termL
       r' <- checkPort fc INPUT  LOGIC termR

       pure (_ ** GateB k o' l' r')

construct curr (Index fc idx t)

  = do (TyPort (flow,BVECT (W (S n) ItIsSucc) type) ** term) <- construct curr t
         | (type ** term)
             => throwAt fc VectorExpected

       case natToFin idx (S n) of
         Nothing => throw (OOB idx (S n))
         Just idx' => do idir <- indexDir fc term
                         pure (_ ** Index idir term idx')

construct curr (Split fc a b i)

  = do termA <- construct curr a
       termB <- construct curr b
       termI <- construct curr i

       a' <- checkPort fc OUTPUT LOGIC termA
       b' <- checkPort fc OUTPUT LOGIC termB
       i' <- checkPort fc INPUT  LOGIC termI

       pure (_ ** Split a' b' i')

construct curr (Collect fc o l r)

  = do termO <- construct curr o
       termL <- construct curr l
       termR <- construct curr r

       o' <- checkPort fc OUTPUT LOGIC termO
       l' <- checkPort fc INPUT  LOGIC termL
       r' <- checkPort fc INPUT  LOGIC termR

       pure (_ ** Collect o' l' r')


construct curr (Stop fc)
  = pure (_ ** Stop)

namespace Design
  export
  check : (ast : AST) -> NetList (Term Nil TyUnit)
  check ast
    = do (TyUnit ** term) <- construct Nil ast
           | (ty ** term) => throw (Mismatch TyUnit ty)
         pure term


-- [ EOF ]
