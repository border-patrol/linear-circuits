|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.Common.Parser

import public Data.Nat
import public Text.Parser

import public Toolkit.Data.Location
import public Toolkit.Text.Lexer.Run
import public Toolkit.Text.Parser.Support
import public Toolkit.Text.Parser.Location
import public Toolkit.Text.Parser.Run

import public Toolkit.Data.Whole

import Circuits.Common.Lexer

import Circuits.Common

%default total

namespace Circuits
  public export
  Rule : Type -> Type
  Rule = Rule Unit Token

  public export
  RuleEmpty : Type -> Type
  RuleEmpty = RuleEmpty Unit Token

  export
  eoi : RuleEmpty Unit
  eoi = eoi isEOI
    where
      isEOI : Token -> Bool
      isEOI EndInput = True
      isEOI _ = False

namespace API

  export
  symbol : String -> Rule Unit
  symbol str
    = terminal ("Expected Symbol '" ++ str ++ "'")
               (\x => case x of
                             Symbol s => if s == str then Just MkUnit
                                                     else Nothing
                             _ => Nothing)

  export
  nat : Rule Nat
  nat = terminal "Expected nat literal"
               (\x => case x of
                           LitNat i => Just i
                           _ => Nothing)

  export
  keyword : String -> Rule Builtin.Unit
  keyword str
    = terminal ("Expected Keyword '" ++ str ++ "'")
                 (\x => case x of
                             Keyword s => if s == str then Just Builtin.MkUnit
                                                      else Nothing
                             _ => Nothing)

  export
  identifier : Rule String
  identifier
    = terminal "Expected Identifier"
               (\x => case x of
                                  ID str => Just str
                                  _ => Nothing)

  export
  name : Rule String
  name = identifier

  export
  ref : Rule Ref
  ref =
    do s <- Toolkit.location
       n <- name
       e <- Toolkit.location
       pure (MkRef (newFC s e) n)


  export
  gives : String -> a -> Rule a
  gives s ctor
    = do keyword s
         pure ctor

  export
  inserts : Rule a -> (a -> b) -> Rule b
  inserts value ctor
    = do v <- value
         pure (ctor v)

  export
  whole : Rule Whole
  whole =
      do n <- nat
         isWhole n
    where
      isWhole : Nat -> RuleEmpty Whole
      isWhole Z = fail "expected whole"
      isWhole (S n) = pure (W (S n) ItIsSucc)

  export
  sFooter : Location -> Rule FileContext
  sFooter s
    = do symbol ")"
         symbol ";"
         e <- Toolkit.location
         pure (newFC s e)

namespace Types

  mutual
    logic : Rule DType
    logic = gives "logic" LOGIC

    array : Rule DType
    array
        = do ty <- logic
             ns <- indices
             pure (arraytype ty (reverse ns))
      where
        mustBeZero : Nat -> Whole -> RuleEmpty Whole
        mustBeZero    Z  (W w prf) = pure (W (S w) ItIsSucc)
        mustBeZero (S n)    w      = fail "No ranges or big endian supported"

        index : Rule Whole
        index
          = do symbol "["
               n <- whole
               symbol ":"
               a <- nat
               symbol "]"
               mustBeZero a n

        indices : Rule (List1 Whole)
        indices = some index

        arraytype : DType -> List1 Whole -> DType
        arraytype ty (x:::xs) = foldl (\ty, n => BVECT n ty) ty (x::xs)

    export
    type : Rule DType
    type = array <|> logic

-- [ EOF ]
