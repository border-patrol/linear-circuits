module Circuits.NetList.Types

import Decidable.Equality


import Data.List.Elem
import Data.Vect
import public Toolkit.Data.Whole
import public Toolkit.Data.Fin
import public Toolkit.Data.DVect
import public Circuits.Common
import Circuits.Common.Pretty

%default total

namespace Direction

  public export
  data Direction = INPUT | OUTPUT | INOUT

  Uninhabited (INPUT = OUTPUT) where
    uninhabited Refl impossible

  Uninhabited (OUTPUT = INOUT) where
    uninhabited Refl impossible

  Uninhabited (INPUT = INOUT) where
    uninhabited Refl impossible

  export
  DecEq Direction where
    decEq INPUT INPUT   = Yes Refl
    decEq INPUT OUTPUT  = No absurd
    decEq INPUT INOUT   = No absurd

    decEq OUTPUT INPUT  = No (negEqSym absurd)
    decEq OUTPUT OUTPUT = Yes Refl
    decEq OUTPUT INOUT  = No absurd

    decEq INOUT INPUT   = No (negEqSym absurd)
    decEq INOUT OUTPUT  = No (negEqSym absurd)
    decEq INOUT INOUT   = Yes Refl

namespace Proj

  public export
  data Project : Direction -> Type where
    WRITE : Project OUTPUT
    READ  : Project INPUT

namespace Cast

  public export
  data Cast : (from,to : Direction) -> Type where
    BI : Cast INOUT INPUT
    BO : Cast INOUT OUTPUT

  Uninhabited (Cast OUTPUT flow) where
    uninhabited BI impossible
    uninhabited BO impossible

  Uninhabited (Cast INPUT flow) where
    uninhabited BI impossible
    uninhabited BO impossible

  Uninhabited (Cast INOUT INOUT) where
    uninhabited BI impossible
    uninhabited BO impossible

  export
  cast : (f,t : Direction) -> Dec (Cast f t)
  cast INPUT _  = No absurd
  cast OUTPUT _ = No absurd
  cast INOUT INPUT = Yes BI
  cast INOUT OUTPUT = Yes BO
  cast INOUT INOUT = No absurd

namespace Index

  public export
  data Up : (flow : Direction) -> Type where
    UO : Up OUTPUT
    UB : Up INOUT

  public export
  data Down : (flow : Direction) -> Type where
    DI : Down INPUT
    DB : Down INOUT

  public export
  data Index : (flow : Direction) -> Type where
    UP   : Up f -> Index f
    DOWN : Down f -> Index f

  export
  dirFromCast : Cast INOUT flow -> Index INOUT
  dirFromCast BI = DOWN DB
  dirFromCast BO = UP UB

namespace Gate

  namespace Binary
    public export
    data Kind = AND  | IOR  | XOR
              | ANDN | IORN | XORN

  namespace Unary
    public export
    data Kind = NOT

    export
    Show Unary.Kind where
      show NOT = "not"

namespace Types

  public export
  data Ty  : Type where
    TyUnit : Ty
    TyPort : (Direction, DType) -> Ty
    TyChan : DType -> Ty
    TyGate : Ty

  Uninhabited (TyUnit = TyPort x) where
    uninhabited Refl impossible

  Uninhabited (TyUnit = TyChan x) where
   uninhabited Refl impossible

  Uninhabited (TyUnit = TyGate) where
    uninhabited Refl impossible

  Uninhabited (TyPort x = TyGate) where
    uninhabited Refl impossible

  Uninhabited (TyPort x = TyChan y) where
    uninhabited Refl impossible

  Uninhabited (TyGate = TyChan y) where
    uninhabited Refl impossible


  export
  DecEq Ty where
    decEq TyUnit TyUnit = Yes Refl
    decEq TyUnit (TyPort x) = No absurd
    decEq TyUnit TyGate = No absurd
    decEq TyUnit (TyChan x) = No absurd

    decEq (TyPort x) TyUnit = No (negEqSym absurd)
    decEq (TyPort x) (TyPort y) with (decEq x y)
      decEq (TyPort x) (TyPort x) | (Yes Refl)
        = Yes Refl
      decEq (TyPort x) (TyPort y) | (No contra)
        = No (\Refl => contra Refl)
    decEq (TyPort x) TyGate = No (absurd)
    decEq (TyPort x) (TyChan c) = No (absurd)

    decEq TyGate TyUnit = No (negEqSym absurd)
    decEq TyGate (TyPort x) = No (negEqSym absurd)
    decEq TyGate TyGate = Yes Refl
    decEq TyGate (TyChan x) = No absurd

    decEq (TyChan ty) TyUnit = No (negEqSym absurd)
    decEq (TyChan ty) (TyPort x) = No (negEqSym absurd)
    decEq (TyChan ty) TyGate = No (negEqSym absurd)
    decEq (TyChan x) (TyChan y) with (decEq x y)
      decEq (TyChan x) (TyChan x) | (Yes Refl) = Yes Refl
      decEq (TyChan x) (TyChan y) | (No contra) = No (\Refl => contra Refl)


export
Show Direction where
  show INPUT  = "input"
  show OUTPUT = "output"
  show INOUT  = "inout"


export
Show (Types.Cast.Cast f t) where
  show BI = "down"
  show BO = "up"

export
Show (Index f) where
  show (UP _) = "UP"
  show (DOWN _) = "DOWN"

export
Show Gate.Binary.Kind where
  show AND  = "and"
  show IOR  = "or"
  show XOR  = "xor"
  show ANDN = "nand"
  show IORN = "nor"
  show XORN = "xnor"

export
Show Ty where
  show TyUnit         = "()"
  show (TyPort (d,t)) = "TyPort(" <+> show d <+> "," <+> show t <+> ")"
  show TyGate         = "TyGate"
  show (TyChan t)     = "TyChan(" <+> show t <+> ")"

namespace DataType
  ||| Is the nested index valid for the datatype
  public export
  data ValidIndex : (i    : List Nat)
                 -> (type : DType)
                 -> (ns   : Vect (length i) Nat)
                 -> (is   : DVect Nat Fin (length i) ns )
                 -> Type
    where
      VHere : NatToFin n (S m) f -> ValidIndex [n]
                                               (BVECT (W (S m)
                                                      ItIsSucc)
                                                      type)
                                               [S m]
                                               [f]

      VThere : NatToFin    n                      (S m)                                    f
            -> ValidIndex     (n'::ns)                            type          (m'::ms)      (f'::fs)
            -> ValidIndex (n::(n'::ns)) (BVECT (W (S m) ItIsSucc) type) (S m :: (m'::ms)) (f::(f'::fs))

  public export
  data ValidIndexResult : (is   : List Nat)
                       -> (type : DType)
                               -> Type
    where
      VIR : (ns : Vect (length i) Nat)
         -> (is : DVect Nat Fin (length i) ns)
         -> (prf : ValidIndex       i type ns is)
                -> ValidIndexResult i type

  Uninhabited (ValidIndex Nil (BVECT n type) ns is) where
    uninhabited (VHere _) impossible

  Uninhabited (ValidIndex as LOGIC ns is) where
    uninhabited (VHere _) impossible


  export
  validIndex : (is   : List Nat)
            -> (type : DType)
                    -> Dec (ValidIndexResult is type)

  validIndex Nil LOGIC       = No (\(VIR ms ns prf) => absurd prf)
  validIndex Nil (BVECT x y) = No (\(VIR ms ns prf) => absurd prf)

  validIndex (x :: xs) LOGIC = No (\(VIR ms ns prf) => absurd prf)

  validIndex (x :: Nil) (BVECT w type) with (w) -- to satisfy the coverage checker.
    validIndex (x :: Nil) (BVECT w type) | (W (S n) ItIsSucc) with (Safe.natToFin x (S n))
      validIndex (x :: Nil) (BVECT w type) | (W (S n) ItIsSucc) | (Yes (idx ** prf))
        = Yes (VIR [S n] [idx] (VHere prf))
      validIndex (x :: Nil) (BVECT w type) | (W (S n) ItIsSucc) | (No no)
        = No (\(VIR [S n] [f] (VHere y)) => no (f ** y))

  validIndex (x :: (x' :: xs)) (BVECT w type) with (w) -- to satisfy the coverage checker.
    validIndex (x :: (x' :: xs)) (BVECT w type) | (W (S n) ItIsSucc) with (Safe.natToFin x (S n))
      validIndex (x :: (x' :: xs)) (BVECT w type) | (W (S n) ItIsSucc) | (Yes (idx ** prf)) with (validIndex (x'::xs) type)
        validIndex (x :: (x' :: xs)) (BVECT w type) | (W (S n) ItIsSucc) | (Yes (idx ** prf)) | (Yes (VIR (y :: ys) (ex :: rest) prfs))
          = Yes (VIR (S n::y::ys) (idx::ex::rest) (VThere prf prfs))

        validIndex (x :: (x' :: xs)) (BVECT w type) | (W (S n) ItIsSucc) | (Yes (idx ** prf)) | (No no)
          = No (\(VIR (S n :: (m' :: ms)) (f' :: (f'' :: fs)) (VThere y z)) => no (VIR (m'::ms) (f''::fs) z))

      validIndex (x :: (x' :: xs)) (BVECT w type) | (W (S n) ItIsSucc) | (No no)
          = No (\(VIR (S n :: (m' :: ms)) (f' :: (f'' :: fs)) (VThere y z)) => no (f' ** y))


||| Is the nested index valid for ports or chans.
public export
data Index : (i    : List Nat)
          -> (type : Ty)
          -> (ns   : Vect (length i) Nat)
          -> (is   : DVect Nat Fin (length i) ns)
                  -> Type
  where
    IP : {ns   : Vect (length i) Nat}
      -> (is  : DVect Nat Fin (length i) ns)
      -> ValidIndex i type ns is
      -> Index i (TyPort (flow,type)) ns is
    IC : {ns   : Vect (length i) Nat}
      -> (is  : DVect Nat Fin (length i) ns)
      -> ValidIndex i type ns is
      -> Index i (TyChan       type)  ns is

Uninhabited (Index i TyGate ns is) where
  uninhabited (IP _ x) impossible

Uninhabited (Index i TyUnit ns is) where
  uninhabited (IP _ x) impossible

public export
data IndexResult : (i : List Nat)
                -> (type : Ty)
                -> Type
  where
    IR : (prf : Index       i type m ms)
             -> IndexResult i type

export
index : (ns   : List Nat)
          -> (type : Ty)
                  -> Dec (IndexResult ns type)

index ns (TyPort (flow, type)) with (validIndex ns type)
  index ns (TyPort (flow, type)) | (Yes (VIR xs is prf))
    = Yes (IR (IP is prf))

  index ns (TyPort (flow, type)) | (No no)
    = No (\(IR (IP _ prf)) => no (VIR _ _ prf))

index ns (TyChan type) with (validIndex ns type)
  index ns (TyChan type) | (Yes (VIR xs is prf))
    = Yes (IR (IC is prf))
  index ns (TyChan type) | (No no)
    = No (\(IR (IC _ prf)) => no (VIR _ _ prf))

index ns TyGate
  = No (\(IR prf) => absurd prf)
index ns TyUnit
  = No (\(IR prf) => absurd prf)


-- [ EOF ]
