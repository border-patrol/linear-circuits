module Circuits.NetList.Parser

import Data.Nat
import Data.List1

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Support
import Toolkit.Text.Parser.Location
import Toolkit.Text.Parser.Run
import Toolkit.Data.Whole

import Ref

import Circuits.NetList.Types
import Circuits.NetList.AST
import Circuits.NetList.Lexer

%default total

namespace NetList
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


namespace Direction
  export
  direction : Rule Direction
  direction = gives "inout" INOUT <|> gives "input" INPUT <|> gives "output" OUTPUT

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
        mustBeZero : Nat -> Whole -> RuleEmpty Whole
        mustBeZero Z (W w prf) = pure (W (S w) ItIsSucc)
        mustBeZero (S n) w = fail "No ranges or big endian supported"

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

namespace Kinds

  export
  gateUnaryKind : Rule Unary.Kind
  gateUnaryKind
           =  gives "not" NOT

  export
  gateBinaryKind : Rule Binary.Kind
  gateBinaryKind
           =  gives "nand" ANDN
          <|> gives "and"  AND
          <|> gives "xor"  XOR
          <|> gives "xnor" XORN
          <|> gives "or"  IOR
          <|> gives "nor" IORN

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
         symbol ";"
         pure ps

  port : Rule AST
  port
      = idx <|> ref'
    where
      ref' : Rule AST
      ref' = pure (Var !ref)

      idx : Rule AST
      idx
        = do s <- Toolkit.location
             r <- ref'
             symbol "["
             w <- nat
             symbol "]"
             e <- Toolkit.location
             pure (Index (newFC s e) w r)

  data Body = WDecl  FileContext DType Ref
            | GInst  FileContext Binary.Kind Ref AST AST AST
            | NInst  FileContext Unary.Kind Ref AST AST
            | MInst  FileContext Ref AST AST AST AST


  gateNot : Rule Body
  gateNot
    = do s <- Toolkit.location
         k <- gateUnaryKind
         n <- ref
         symbol "("
         o <- port
         symbol ","
         i <- port
         symbol ")"
         symbol ";"
         e <- Toolkit.location
         pure (NInst (newFC s e) k n o i)

  gateBin : Rule Body
  gateBin
    = do s <- Toolkit.location
         k <- gateBinaryKind
         n <- ref
         symbol "("
         o <- port
         symbol ","
         a <- port
         symbol ","
         b <- port
         symbol ")"
         symbol ";"
         e <- Toolkit.location
         pure (GInst (newFC s e) k n o a b)

  gateMux : Rule Body
  gateMux
    = do s <- Toolkit.location
         keyword "mux"
         n <- ref
         symbol "("
         o <- port
         symbol ","
         c <- port
         symbol ","
         a <- port
         symbol ","
         b <- port
         symbol ")"
         symbol ";"
         e <- Toolkit.location
         pure (MInst (newFC s e) n o c a b)



  wireDecl : Rule Body
  wireDecl
      = do s <- Toolkit.location
           keyword "wire"
           t <- type
           a <- ref
           symbol ";"
           e <- Toolkit.location
           pure (WDecl (newFC s e) t a)

  expr : Rule Body
  expr = wireDecl <|> gateNot <|> gateBin <|> gateMux

  foldBody : Location
          -> List Body
          -> AST
  foldBody l bs
        = foldr doFold (Stop (newFC l l)) bs
    where
      doFold : Body -> AST -> AST

      doFold (WDecl x y z) accum
        = Wire x y z accum

      doFold (MInst v n w x y z) accum
        = GateDecl v n (Mux v w x y z) accum

      doFold (GInst x k n y z w) accum
        = GateDecl x n (GateB x k y z w) accum

      doFold (NInst x k n y z) accum
        = GateDecl x n (GateU x k y z) accum

  foldPorts : Location
           -> List1 (Location,Ref, Direction, DType)
           -> AST
           -> AST
  foldPorts e (x:::xs) y
    = foldr (\(s,r,d,t), body => Port (newFC s e) d t r body) y (x::xs)

  export
  design : Rule AST
  design
    = do keyword "module"
         n <- ref
         ps <- portList
         b <- many expr
         e <- Toolkit.location
         keyword "endmodule"
         symbol ";"
         pure (foldPorts e ps (foldBody e b))

namespace Idealised

  export
  fromFile : (fname : String)
                   -> IO (Either (ParseError Token) AST)
  fromFile fname
    = case !(parseFile Idealised.Lexer design fname) of
        Left err  => pure (Left err)
        Right ast => pure (Right (setSource fname ast)) -- @TODO add name
-- [ EOF ]
