||| Using Channels
|||
||| Module    : Channel/Use.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Circuits.NetList.Linear.Usage.TermType.Channel.Use

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Data.Vect
import Data.Vect.AtIndex
import Data.Vect.Quantifiers

import Data.String

import Toolkit.Data.Whole
import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DVect

import Circuits.Common

import Circuits.NetList.Types

import Circuits.NetList.Linear.Usage.DataType
import Circuits.NetList.Linear.Usage.DataType.Use.Full
import Circuits.NetList.Linear.Usage.DataType.Use.Partial

import Circuits.NetList.Linear.Usage.TermType
import Circuits.NetList.Linear.Usage.TermType.Channel

%default total

namespace Channel
  public export
  data Use : (how  : Project dir)
          -> (type : Ty)
          -> (old  : Usage type)
          -> (prf  : CanProject how type old)
          -> (new  : Usage type)
                  -> Type

    where
      IsWrite : Use               type          ein                     free          newU       prf
             -> Use WRITE (TyChan type) (TyChan ein eout) (ProjectWrite free) (TyChan newU eout)

      IsRead : Use              type             eout               free              newU  prf
            -> Use READ (TyChan type)(TyChan ein eout) (ProjectRead free) (TyChan ein newU)

  namespace Full
    public export
    data Result : (how  : Project dir)
               -> (type : Ty)
               -> (old  : Usage type)
               -> (prf  : CanProject how type old)
                       -> Type
      where
        R : (new : Usage  (TyChan type))
         -> (prf : Use    how (TyChan type) old proj new)
                -> Result how (TyChan type) old proj

  export
  use : {old : Usage type}
     -> (prf : CanProject how type old)
            -> Result     how type old prf
  use (ProjectWrite prf) with (use prf)
    use (ProjectWrite prf) | (R u used result)
      = R (TyChan u _) (IsWrite result)
  use (ProjectRead prf) with (use prf)
    use (ProjectRead prf) | (R u used result)
      = R (TyChan _ u) (IsRead result)


  public export
  data UseAt : (how  : Project dir)
            -> (idx  : List Nat)
            -> (type : Ty)
            -> (old  : Usage type)
            -> (prf  : CanProjectAt how idx type old)
            -> (new  : Usage type)
                    -> Type

    where
      IsWriteAt : UseAt       idx         (BVECT (W (S n) ItIsSucc) type)          ein                       free          newU       prf
               -> UseAt WRITE idx (TyChan (BVECT (W (S n) ItIsSucc) type)) (TyChan ein eout) (ProjectAtWrite free) (TyChan newU eout)

      IsReadAt : UseAt      idx         (BVECT (W (S n) ItIsSucc) type)              eout                 free              newU  prf
              -> UseAt READ idx (TyChan (BVECT (W (S n) ItIsSucc) type)) (TyChan ein eout) (ProjectAtRead free) (TyChan ein newU)

  namespace Partial
    public export
    data Result : (how  : Project dir)
               -> (idx  : List Nat)
               -> (type : Ty)
               -> (old  : Usage type)
               -> (prf  : CanProjectAt how idx type old)
                       -> Type
      where
        R : {idx  : List Nat}
         -> {proj : CanProjectAt how idx (TyChan type) old}
         -> (new : Usage  (TyChan type))
         -> (prf : UseAt  how idx (TyChan type) old proj new)
                -> Result how idx (TyChan type) old proj


  export
  useAt : {idx  : List Nat}
       -> {old : Usage type}
       -> (prf : CanProjectAt how idx type old)
              -> Result       how idx type old prf
  useAt (ProjectAtWrite prf) with (prf)
    useAt (ProjectAtWrite prf) | p' with (useAt _ p')
      useAt (ProjectAtWrite prf) | p' | (R (Array us) (UsedAtHere x) holds)
        = R (TyChan (Array us) _) (IsWriteAt holds)
      useAt (ProjectAtWrite prf) | p' | (R (Array us) (UsedAtThere x) holds)
        = R (TyChan (Array us) _) (IsWriteAt holds)

  useAt (ProjectAtRead prf) with (prf)
    useAt (ProjectAtRead prf) | p' with (useAt _ p')
      useAt (ProjectAtRead prf) | p' | (R (Array us) (UsedAtHere x) holds)
        = R (TyChan _ (Array us)) (IsReadAt holds)
      useAt (ProjectAtRead prf) | p' | (R (Array us) (UsedAtThere x) holds)
        = R (TyChan _ (Array us)) (IsReadAt holds)

-- [ EOF ]
