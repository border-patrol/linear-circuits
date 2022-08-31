module Circuits.NetList.Linear.Check

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List1
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

import Circuits.NetList.Linear.AST
import Circuits.NetList.Linear.Usage
import Circuits.NetList.Linear.Terms

import Circuits.NetList.Linear.Check.API
import Circuits.NetList.Linear.Check.Lookup
import Circuits.NetList.Linear.Check.Elab
import Circuits.NetList.Linear.Check.Stop

%default total

construct : {cin  : List Item}
         -> (curr : Context cin)
         -> (ast  : AST)
                 -> Linear (DPair Ty (Result cin))

-- [ NOTE ]
--
-- This will return gates, and ports & chans that are fully used.
construct curr (Ref (MkRef fc str))
  = Full.lookup fc str curr

-- [ NOTE ] Bindable things

construct curr (Port fc flow ty n scope)
  = do let (i ** prf) = init flow ty
       let currExt = extend curr (get n) i

       (TyUnit ** (R Nil term)) <- construct currExt
                                             scope
         | (ty ** (R xs _)) => throw (ErrI "Internal error")
         | (ty ** _) => throw (Mismatch TyUnit ty)

       pure (_ ** R Nil (Port flow ty prf term))

construct curr (Wire fc type n scope)
  = do let (i ** prf) = Channel.init type
       let currExt = extend curr (get n) i

       (TyUnit ** (R Nil term)) <- construct currExt
                                             scope
         | (ty ** (R xs _)) => throw (ErrI "Internal error")
         | (ty ** _) => throw (Mismatch TyUnit ty)

       pure (_ ** R Nil (Wire type prf term))

construct curr (GateDecl fc n g scope)
  = do (TyGate ** R cG gate) <- construct curr g
         | (type ** _) => throwAt fc (Mismatch TyGate type)

       let currExt = extend cG (get n) (I TyGate TyGate)

       (TyUnit ** R Nil term) <- construct currExt scope
         | (ty ** (R xs _)) => throw (ErrI "Internal error")
         | (ty ** _) => throw (Mismatch TyUnit ty)

       pure (_ ** R Nil (Gate gate term))


-- [ NOTE ] Ensure direction is correct.
construct curr (Shim fc edir term)
  = do result <- construct curr term

       dtype <- getDataType fc result

       result <- checkPort fc edir dtype result
       pure (_ ** result)


-- [ NOTE ] Assignments
construct curr (Assign fc o i scope)
  = do termO <- construct curr o
       (R cO o) <- checkPort (getFC o) OUTPUT LOGIC termO

       termI <- construct cO i
       (R cI i) <- checkPort (getFC i) INPUT LOGIC termI

       (TyUnit ** R Nil term) <- construct cI scope
         | (ty ** (R xs _)) => throw (ErrI "Internal error")
         | (ty ** _) => throw (Mismatch TyUnit ty)

       pure (_ ** R Nil (Assign o i term))

-- [ NOTE ] Gates
construct curr (Mux fc o c l r)
  = do termO <- construct curr o
       (R cO o) <- checkPort (getFC o) OUTPUT LOGIC termO

       termC <- construct cO c
       (R cC c) <- checkPort (getFC c) INPUT LOGIC termC

       termL <- construct cC l
       (R cL l) <- checkPort (getFC l) INPUT LOGIC termL

       termR <- construct cL r
       (R cR r) <- checkPort (getFC r) INPUT LOGIC termR

       pure (_ ** R cR (Mux o c l r))

construct curr (GateU fc k o i)
  = do termO <- construct curr o
       (R cO o) <- checkPort (getFC o) OUTPUT LOGIC termO

       termI <- construct cO i
       (R cI i) <- checkPort (getFC i) INPUT LOGIC termI

       pure (_ ** R cI (GateU k o i))

construct curr (GateB fc k o l r)
  = do termO <- construct curr o
       (R cO o) <- checkPort (getFC o) OUTPUT LOGIC termO

       termL <- construct cO l
       (R cL l) <- checkPort (getFC l) INPUT LOGIC termL

       termR <- construct cL r
       (R cR r) <- checkPort (getFC r) INPUT LOGIC termR

       pure (_ ** R cR (GateB k o l r))

-- [ NOTE ] Indexing
construct curr (Index fc d is ref)
  = do let is = map Builtin.snd (forget is)
       Partial.lookup fc d is (get ref) curr


-- [ NOTE ]
--
-- Linear operations
construct curr (Split fc a b i)
  = do termA <- construct curr a

       (R cA a') <- checkPort (getFC a) OUTPUT LOGIC termA

       termB <- construct cA b

       (R cB b') <- checkPort (getFC b) OUTPUT LOGIC termB

       termI <- construct cB i

       (R cI i') <- checkPort (getFC i) INPUT  LOGIC termI

       pure (_ ** R cI (Split a' b' i'))

construct curr (Collect fc o l r)
  = do termO <- construct curr o
       (R cO o) <- checkPort (getFC o) OUTPUT LOGIC termO

       termL <- construct cO l
       (R cL l) <- checkPort (getFC l) INPUT LOGIC termL

       termR <- construct cL r

       (R cR r) <- checkPort (getFC r) INPUT  LOGIC termR

       pure (_ ** R cR (Collect o l r))



-- [ Stopping ]
construct curr (Stop fc)
  = do prf <- canStop fc curr
       pure (_ ** R Nil (Stop prf))



||| Only work with closed designs.
namespace Design

  export
  check : (ast : AST)
              -> Linear (Term Nil TyUnit Nil)
  check ast
    = do (TyUnit ** R Nil term) <- construct Nil ast
           | (ty ** (R xs _)) => throw (ErrI "Internal error")
           | (ty ** _) => throw (Mismatch TyUnit ty)
         pure term


-- [ EOF ]
