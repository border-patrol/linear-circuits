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

public export
data HasData : (type  : Ty)
            -> (dtype : DType)
                     -> Type
  where
    HDP : (d : DType) -> HasData (TyPort (flow,d)) d
    HDC : (d : DType) -> HasData (TyChan d)        d

Uninhabited (HasData TyGate type) where
  uninhabited (HDP d) impossible

Uninhabited (HasData TyUnit type) where
  uninhabited (HDP d) impossible

data HasDataResult : (type : Ty)
                          -> Type
  where
    HDR : HasData type dtype -> HasDataResult type

export
hasData : (type : Ty) -> Dec (HasDataResult type)

hasData (TyPort (f,d))
  = Yes (HDR (HDP d))

hasData (TyChan d)
  = Yes (HDR (HDC d))

hasData TyGate = No (\(HDR prf) => absurd prf)
hasData TyUnit = No (\(HDR prf) => absurd prf)

-- [ EOF ]
