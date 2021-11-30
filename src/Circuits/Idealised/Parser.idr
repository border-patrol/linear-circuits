module Circuits.Idealised.Parser

import Data.List1

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Support
import Toolkit.Text.Parser.Location
import Toolkit.Text.Parser.Run

import Ref

import Circuits.Types
import Circuits.Idealised.AST
import Circuits.Idealised.Lexer

%default total

namespace Idealised
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

namespace Direction
  export
  direction : Rule Direction
  direction = gives "input" INPUT <|> gives "output" OUTPUT

namespace Types

  mutual
    logic : Rule DType
    logic = gives "logic" LOGIC

    array : Rule DType
    array
        = do ty <- logic
             ns <- indices
             pure (arraytype ty ns)
      where
        index : Rule Nat
        index
          = do symbol "["
               n <- nat
               symbol "]"
               pure n

        indices : Rule (List1 Nat)
        indices = some index

        arraytype : DType -> List1 Nat -> DType
        arraytype ty (x:::xs) = foldl (\ty, n => BVECT n ty) ty (x::xs)

    export
    type : Rule DType
    type = logic <|> array

namespace Terms

  portDecl : Rule (Location, Ref, Direction, DType)
  portDecl
    = do s <- Toolkit.location
         d <- direction
         t <- type
         r <- ref
         pure (s,r,d,t)

  portList : Rule (List1 (Location,Ref, Direction, DType))
  portList
    = do symbol "("
         ps <- sepBy1 (symbol ",") portDecl
         symbol ")"
         pure ps

  mutual
    gateN : Rule AST
    gateN
      = do s <- Toolkit.location
           keyword "not"
           symbol "("
           o <- ref
           symbol ","
           i <- ref
           symbol ")"
           symbol ";"
           e <- Toolkit.location
           pure (Not (newFC s e) (Var o) (Var i))

    gate : Rule AST
    gate
      = do s <- Toolkit.location
           keyword "gate"
           symbol "("
           o <- ref
           symbol ","
           a <- ref
           symbol ","
           b <- ref
           symbol ")"
           symbol ";"
           e <- Toolkit.location
           pure (Gate (newFC s e) (Var o) (Var a) (Var b))

  gates : Rule AST
  gates
      = do gs <- some (gate <|> gateN)
           s <- Toolkit.location
           pure (foldr Seq (Stop (newFC s s)) (forget gs))

  mutual
    wire : Rule AST
    wire
      = do s <- Toolkit.location
           keyword "wire"
           t <- type
           keyword "as"
           symbol "("
           a <- ref
           symbol ","
           b <- ref
           symbol ")"
           symbol ";"
           rest <- body
           e <- Toolkit.location
           pure (Wire (newFC s e) t a b rest)

    body : Rule AST
    body = wire <|> gates

  build : Location
       -> List (Location,Ref, Direction, DType)
       -> AST
       -> AST
  build e xs y = foldr (\(s,r,d,t), body => Input (newFC s e) d t r body) y xs

  export
  design : Rule AST
  design
    = do keyword "circuit"
         ps <- portList
         symbol "{"
         b <- body
         e <- Toolkit.location
         symbol "}"
         pure (build e (forget ps) b)

namespace Idealised

  export
  fromFile : (fname : String)
                   -> IO (Either (ParseError Token) AST)
  fromFile fname
    = case !(parseFile Idealised.Lexer design fname) of
        Left err  => pure (Left err)
        Right ast => pure (Right ast) -- @TODO add name
-- [ EOF ]
