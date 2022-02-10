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
  direction = gives "inout"  INOUT
          <|> gives "input"  INPUT
          <|> gives "output" OUTPUT

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

  shim : Direction -> Rule AST -> Rule AST
  shim d port
    = do s <- Toolkit.location
         p <- port
         e <- Toolkit.location
         pure (Shim (newFC s e) d p)

  port : Direction -> Rule AST
  port d
      = (shim d idx) <|> (shim d ref')
    where

      ref' : Rule AST
      ref' = pure (Var !ref)

      value : Rule (Pair Nat Location)
      value
        = do symbol "["
             n <- nat
             symbol "]"
             e <- Toolkit.location
             pure (n,e)

      indices : Rule (List1 (Nat, Location))
      indices
        = some value

      build : Location
            -> AST
            -> List1 (Nat,Location)
            -> AST
      build s first (x:::xs)
        = foldl (\i, (n,e) => Index (newFC s e) n i) first (x::xs)

      idx : Rule AST
      idx
        = do s <- Toolkit.location
             r <- ref'
             is <- indices
             pure (build s r is)

  data Body = WDecl  FileContext DType Ref
            | GInst  FileContext Binary.Kind Ref AST AST AST
            | NInst  FileContext Unary.Kind Ref AST AST
            | MInst  FileContext Ref AST AST AST AST
            | AInst  FileContext AST AST
            | CInst  FileContext Ref AST AST AST
            | SInst  FileContext Ref AST AST AST


  assign : Rule Body
  assign
    = do s <- Toolkit.location
         keyword "assign"
         o <- port OUTPUT
         symbol "="
         i <- port INPUT
         symbol ";"
         e <- Toolkit.location
         pure (AInst (newFC s e) i o)

  gateNot : Rule Body
  gateNot
    = do s <- Toolkit.location
         k <- gateUnaryKind
         n <- ref
         symbol "("
         o <- port OUTPUT
         symbol ","
         i <- port INPUT
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
         o <- port OUTPUT
         symbol ","
         a <- port INPUT
         symbol ","
         b <- port INPUT
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
         o <- port OUTPUT
         symbol ","
         c <- port INPUT
         symbol ","
         a <- port INPUT
         symbol ","
         b <- port INPUT
         symbol ")"
         symbol ";"
         e <- Toolkit.location
         pure (MInst (newFC s e) n o c a b)


  collect : Rule Body
  collect
    = do s <- Toolkit.location
         keyword "collect"
         n <- ref
         symbol "("
         o <- port OUTPUT
         symbol ","
         a <- port INPUT
         symbol ","
         b <- port INPUT
         symbol ")"
         symbol ";"
         e <- Toolkit.location
         pure (CInst (newFC s e) n o a b)

  split : Rule Body
  split
    = do s <- Toolkit.location
         keyword "split"
         n <- ref
         symbol "("
         o <- port OUTPUT
         symbol ","
         a <- port OUTPUT
         symbol ","
         b <- port INPUT
         symbol ")"
         symbol ";"
         e <- Toolkit.location
         pure (SInst (newFC s e) n o a b)

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
  expr = assign <|> wireDecl <|> gateNot <|> gateBin <|> gateMux

  foldBody : Location
          -> List Body
          -> AST
  foldBody l bs
        = foldr doFold (Stop (newFC l l)) bs
    where
      doFold : Body -> AST -> AST

      doFold (WDecl x y z)
        = Wire x y z

      doFold (MInst v n w x y z)
        = GateDecl v n (Mux v w x y z)

      doFold (GInst x k n y z w)
        = GateDecl x n (GateB x k y z w)

      doFold (NInst x k n y z)
        = GateDecl x n (GateU x k y z)

      doFold (AInst fc i o)
        = Assign fc i o

      doFold (CInst fc n o a b)
        = GateDecl fc n (Collect fc o a b)

      doFold (SInst fc n o a b)
        = GateDecl fc n (Split fc o a b)

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
    = case !(parseFile NetList.Lexer design fname) of
        Left err  => pure (Left err)
        Right ast => pure (Right (setSource fname ast))

-- [ EOF ]
