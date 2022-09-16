||| Update usage predicates.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.DataType.Use.Full

import Decidable.Equality
import Toolkit.Decidable.Informative

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers
import Data.Vect.Quantifiers
import Data.Vect
import Data.Vect.AtIndex

import Data.String

import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Extra
import Toolkit.Data.Vect.Quantifiers

import Circuits.Common
import Circuits.NetList.Types
import Circuits.NetList.Linear.Usage.DataType

%default total

-- # [ Definitions ]

mutual

-- ## [ Use All the Things ]

  public export
  data Use : (type : DType)
          -> (free : Usage  type)
          -> (this : IsFree type free)
          -> (used : Usage  type)
          -> (that : IsUsed type used)
                  -> Type
    where
      UFL : Use LOGIC (Logic FREE) FreeL
                      (Logic USED) UsedL

      UFA : (prf : Use type fs free us used)
                -> Use (BVECT (W (S n) ItIsSucc) type) (Array fs) (FreeA free)
                                                       (Array us) (UsedA used)

  namespace Vect
    public export
    data Use : (type : DType)
            -> (this : Vect n (Usage  type))
            -> (free : All    (IsFree type) this)
            -> (that : Vect n (Usage  type))
            -> (used : All    (IsUsed type) that)
                    -> Type
      where
        End : Use type     Nil       Nil      Nil      Nil
        Ext : Use type  f        pf        u       pu
           -> Use type     fs        pfs      us       pus
           -> Use type (f::fs)  (pf::pfs) (u::us) (pu::pus)

-- ## [ Return Results ]

  public export
  data Result : (type : DType)
             -> (free : Usage  type)
             -> (prf  : IsFree type free)
                     -> Type
    where
      R : (u      : Usage  type)
       -> (used   : IsUsed type        u)
       -> (result : Use    type f free u used)
                 -> Result type f free

  namespace Vect

    public export
    data Result : (type : DType)
               -> (free : Vect n (Usage type))
               -> (prf  : All (IsFree type) free)
                       -> Type
      where
        R : {this    : Vect n (Usage type)}
         -> (free    : All (IsFree type) this)
         -> (us      : Vect n (Usage type))
         -> (useds   : All (IsUsed type) us)
         -> (results : Use    type this free us useds)
                    -> Result type this free


-- # [ Actually Use All the Things ]

mutual

  export
  use : {free : Usage type}
     -> (prf  : IsFree type free)
             -> Result type free prf

  use FreeL
    = R (Logic USED) UsedL UFL

  use (FreeA prf) with (use prf)
    use (FreeA prf) | (R prf us useds results)
      = R (Array us) (UsedA useds) (UFA results)

  namespace Vect
    export
    use : {free : Vect n (Usage type)}
       -> (prf  : All (IsFree type) free)
               -> Result type free prf
    use []
      = R [] [] [] End

    use (x :: xs) with (use x)
      use (x :: xs) | (R u used result) with (use xs)
        use (x :: xs) | (R u used result) | (R xs us useds results)
          = R (x :: xs)
              (u :: us)
              (used :: useds)
              (Ext result results)

-- [ EOF ]
