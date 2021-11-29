module Circuits.Types

import Data.List.Elem

%default total

public export
data Usage = USED | FREE

public export
data Direction = INPUT | OUTPUT

public export
data DType = LOGIC | BVECT Nat DType

public export
data PortHasProperties : Direction -> DType -> (Direction, DType) -> Type
  where
    PortHas : PortHasProperties flow type (flow,type)

public export
data Ty : Type where
  Unit : Ty
  Port : (Direction, DType) -> Ty

  Gate : Ty

public export
data Used : (Ty, Usage) -> Type where
  IsUsed : Used (type, USED)

public export
data Use : (old : List (Ty, Usage))
        -> (prf : Elem (type,FREE) old)
        -> (new : List (Ty, Usage))
        -> Type
  where
    H : Use ((type,FREE) :: rest)
            Here
            ((type,USED) :: rest)
    T : Use old later new
     -> Use ((type',usage')::old) (There later) ((type',usage')::new)


-- [ EOF ]
