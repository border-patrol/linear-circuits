module Circuits.NetList.Check

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List.Elem
import Data.List.Quantifiers
import Data.Fin

import Toolkit.Decidable.Informative

import Toolkit.Data.Location
import Toolkit.Data.Whole
import Toolkit.Data.List.DeBruijn

import Circuits.NetList.Types
import Circuits.NetList.Terms
import Circuits.NetList.AST

%default total

data Entry : (String,Ty) -> Type where
  MkEntry : (name : String)
         -> (type : Ty)
                 -> Entry (MkPair name type)

Env : List (String,Ty) -> Type
Env = Env (String,Ty) Entry


public export
data Error = Mismatch Ty Ty
           | MismatchD DType DType
           | NotBound String
           | VectorExpected
           | PortChanExpected
           | PortExpected
           | OOB Nat Nat
           | ErrI String
           | Err FileContext Error

strip : {ctxt : List (String, Ty)}
     -> Elem (s,type) ctxt -> Elem type (map Builtin.snd ctxt)
strip Here = Here
strip (There x) = There (strip x)

public export
TyCheck : Type -> Type
TyCheck = Either Error

lift : Dec a -> Error -> TyCheck a
lift (Yes prf) _ = Right prf
lift (No contra) e = Left e

namespace Elab

  export
  getDataType : FileContext
             -> (term : (type ** Term ctxt type))
                     -> TyCheck DType
  getDataType fc (MkDPair (TyPort (d,x)) snd) = pure x
  getDataType fc (MkDPair (TyChan x) snd) = pure x
  getDataType fc (MkDPair type snd)
    = Left (Err fc PortChanExpected)

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

  ||| When casting we finally know which direction indexing should go, so lets fix that.
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

  portCast : {type : DType}
        -> {flow : Direction}
        -> FileContext
        -> (expected : Direction)
        -> (term : Term ctxt (TyPort (flow,type)))
                -> TyCheck (Term ctxt (TyPort (expected,type)))

  portCast {type} {flow = flow} fc exp term with (shouldCast flow exp term)
    portCast {type} {flow = flow} fc exp term | Yes (p,e)
      = Right e
    portCast {type} {flow = flow} fc exp term | No contra with (decEq flow exp)
      portCast {type} {flow = exp} fc exp term | No contra | (Yes Refl)
        = Right term
      portCast {type} {flow = flow} fc exp term | No contra | (No f)
        = Left (Err fc (Mismatch (TyPort (exp,type)) (TyPort (flow,type))))

  export
  checkPort : (fc    : FileContext)
           -> (exdir : Direction)
           -> (expty : DType)
           -> (term  : (type ** Term ctxt type))
                    -> TyCheck (Term ctxt (TyPort (exdir,expty)))

  -- [ NOTE ]
  --
  checkPort fc exdir exty (MkDPair (TyPort (given,x)) term)
    = do Refl <- lift (decEq exty x)
                      (Err fc (MismatchD exty x))

         portCast fc exdir term

  -- [ NOTE ]
  --
  -- READ implies INPUT
  checkPort fc INPUT exty (MkDPair (TyChan x) term)
    = do Refl <- lift (decEq exty x)
                      (Err fc (MismatchD exty x))

         pure (Project READ term)

  -- [ NOTE ]
  --
  -- WRITE implies OUTPUT
  checkPort fc OUTPUT exty (MkDPair (TyChan x) term)
    = do Refl <- lift (decEq exty x)
                      (Err fc (MismatchD exty x))

         Right (Project WRITE term)

  -- [ NOTE ]
  --
  -- INOUT Chan's impossible.
  checkPort fc INOUT exty (MkDPair (TyChan x) term)
     = Left (Err fc (ErrI "INOUT CHAN not expected"))


  -- [ NOTE ]
  --
  -- Gates/TyUnit not expected
  checkPort fc exdir exty (MkDPair type term)
     = Left (Err fc (Mismatch (TyPort (exdir,exty)) type))

  export
  indexDir : {flow : Direction}
          -> (fc   : FileContext)
          -> (term : Term ctxt (TyPort (flow,BVECT (W (S n) ItIsSucc) type)))
                  -> TyCheck (Index flow)
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
      = Left (Err fc (ErrI "Shouldn't happen impossible indexing a projection with inout"))
    indexDir {flow = flow} fc (Cast x what) | INOUT
      = Left (Err fc (ErrI "Shouldn't happen impossible indexing a cast with inout"))

namespace TypeCheck
  export
  typeCheck : {ctxt : List (String,Ty)}
           -> (curr : Env ctxt)
           -> (ast  : AST)
                    -> TyCheck (DPair Ty (Term (map Builtin.snd ctxt)))


  typeCheck {ctxt} curr (Var x)
    = do (ty ** prf) <- lift (isIndex (get x) ctxt)
                             (Err (span x) (NotBound (get x)))

         pure (ty ** Var (strip prf))

  typeCheck curr (Port fc flow ty n body)
    = do (TyUnit ** term) <- typeCheck (MkEntry (get n) (TyPort (flow,ty))::curr) body
           | (type ** _) => Left (Err fc (Mismatch TyUnit type))

         pure (_ ** Port flow ty term)

  typeCheck curr (Wire fc ty n body)
    = do (TyUnit ** term) <- typeCheck (MkEntry (get n) (TyChan ty)::curr) body
           | (type ** _) => Left (Err fc (Mismatch TyUnit type))

         pure (_ ** Wire ty term)

  typeCheck curr (GateDecl fc n g body)
    = do (TyGate ** gate) <- typeCheck curr g
           | (type ** _) => Left (Err fc (Mismatch TyGate type))

         (TyUnit ** term) <- typeCheck (MkEntry (get n) (TyGate)::curr) body
           | (type ** _) => Left (Err fc (Mismatch TyUnit type))

         pure (_ ** GateDecl gate term)

  typeCheck curr (Assign fc i o rest)
    =  do termI <- typeCheck curr i

          ity <- getDataType fc termI

          termO <- typeCheck curr o
          oty <- getDataType fc termO

          Refl <- lift (decEq ity oty)
                       (Err fc (MismatchD ity oty))

          i' <- checkPort fc INPUT  ity termI
          o' <- checkPort fc OUTPUT ity termO


          (TyUnit ** r') <- typeCheck curr rest
           | (type ** _) => Left (Err fc (Mismatch TyUnit type))

          pure (_ ** Assign i' o' r')


  typeCheck curr (Mux fc o c l r)
    = do termO <- typeCheck curr o
         termC <- typeCheck curr c
         termL <- typeCheck curr l
         termR <- typeCheck curr r

         o' <- checkPort fc OUTPUT LOGIC termO
         c' <- checkPort fc INPUT  LOGIC termC
         l' <- checkPort fc INPUT  LOGIC termL
         r' <- checkPort fc INPUT  LOGIC termR

         pure (_ ** Mux o' c' l' r')

  typeCheck curr (GateU fc k o i)
    = do termO <- typeCheck curr o
         termI <- typeCheck curr i

         o' <- checkPort fc OUTPUT LOGIC termO
         i' <- checkPort fc INPUT  LOGIC termI

         pure (_ ** GateU k o' i')

  typeCheck curr (GateB fc k o l r)

    = do termO <- typeCheck curr o
         termL <- typeCheck curr l
         termR <- typeCheck curr r

         o' <- checkPort fc OUTPUT LOGIC termO
         l' <- checkPort fc INPUT  LOGIC termL
         r' <- checkPort fc INPUT  LOGIC termR

         pure (_ ** GateB k o' l' r')

  typeCheck curr (Index fc idx t)

    = do (TyPort (flow,BVECT (W (S n) ItIsSucc) type) ** term) <- typeCheck curr t
           | (type ** term)
               => Left (Err fc VectorExpected)

         case natToFin idx (S n) of
           Nothing => Left (OOB idx (S n))
           Just idx' => do idir <- indexDir fc term
                           pure (_ ** Index idir term idx')

  typeCheck curr (Split fc a b i)

    = do termA <- typeCheck curr a
         termB <- typeCheck curr b
         termI <- typeCheck curr i

         a' <- checkPort fc OUTPUT LOGIC termA
         b' <- checkPort fc OUTPUT LOGIC termB
         i' <- checkPort fc INPUT  LOGIC termI

         pure (_ ** Split a' b' i')

  typeCheck curr (Collect fc o l r)
    = do (TyPort (OUTPUT,BVECT (W (S (S Z)) ItIsSucc) type) ** o') <- typeCheck curr o
           | (TyPort (flow,BVECT (W (S (S n)) ItIsSucc) type) ** term)
               => Left (Err fc (Mismatch (TyPort (OUTPUT, BVECT (W (S (S Z)) ItIsSucc) type))
                                         (TyPort (flow,   BVECT (W (S (S n)) ItIsSucc) type))
                                         ))
           | (type ** term)
               => Left (Err fc VectorExpected)

         termL <- typeCheck curr l
         termR <- typeCheck curr r

         l' <- checkPort fc INPUT  type termL
         r' <- checkPort fc INPUT  type termR

         pure (_ ** Collect o' l' r')

  typeCheck curr (Shim fc dir thing)

    = do t <- typeCheck curr thing

         dtype <- getDataType fc t

         term <- checkPort fc dir dtype t

         pure (_ ** term)

  typeCheck curr (Stop x)
    = pure (_ ** Stop)

namespace Design
  export
  typeCheck : (ast : AST) -> TyCheck (Term Nil TyUnit)
  typeCheck ast with (typeCheck Nil ast)
    typeCheck ast | (Left x) = Left x
    typeCheck ast | (Right (MkDPair TyUnit term)) = Right term
    typeCheck ast | (Right (MkDPair ty snd)) = Left (Mismatch TyUnit ty)

  export
  typeCheckIO : (ast : AST) -> IO (TyCheck (Term Nil TyUnit))
  typeCheckIO ast = pure (typeCheck ast)

-- [ EOF ]
