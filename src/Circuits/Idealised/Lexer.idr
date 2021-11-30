module Circuits.Idealised.Lexer

import Text.Lexer

import Toolkit.Text.Lexer.Run

%default total


symbols : List String
symbols = ["->", "-", "[", "]", ";", "{", "}", ":", ",", "=", "?", "(", ")", ".", "#", "!", "&", "|", "+"]

keywords : List String
keywords = [ "input", "output"
           , "circuit", "wire"
           , "logic", "as", "in"
           , "gate", "not"
           ]

public export
data Identifier = MkIdentifier String

export
Eq Identifier where
  (==) (MkIdentifier x) (MkIdentifier y) = x == y

namespace Idealised
  public export
  data Token = ID String
               | Keyword String
               | LineComment String
               | BlockComment String
               | Documentation String
               | LitNat Nat
               | Symbol String
               | WS String
               | NotRecognised String
               | EndInput

  export
  Eq Token where
    (==) (ID x) (ID y) = x == y
    (==) (LineComment x) (LineComment y) = x == y
    (==) (BlockComment x) (BlockComment y) = x == y
    (==) (LitNat x) (LitNat y) = x == y
    (==) (Documentation x) (Documentation y) = x == y
    (==) (Keyword x) (Keyword y) = x == y
    (==) (Symbol x) (Symbol y) = x == y
    (==) (WS x) (WS y) = x == y
    (==) (NotRecognised x) (NotRecognised y) = x == y
    (==) EndInput EndInput = True
    (==) _ _ = False


  identifier : Lexer
  identifier = pred startIdent <+> many (pred validIdent)
    where
      startIdent : Char -> Bool
      startIdent x = isAlpha x

      validIdent : Char -> Bool
      validIdent '_' = True
      validIdent x = isAlphaNum x



  export
  tokenMap : TokenMap Idealised.Token
  tokenMap = with List
    [
      (space, WS)
    , (lineComment (exact "//"), LineComment)
    , (blockComment (exact "/*") (exact "*/"), BlockComment)
    , (lineComment (exact "\\\\"), Documentation)
    , (digits, \x => LitNat (integerToNat $ cast {to=Integer} x))
    ]
    ++
       map (\x => (exact x, Symbol)) symbols
    ++
    [
      (identifier, (\x => if elem x keywords then Keyword x else ID x))
    , (any, NotRecognised)
    ]

  keep : WithBounds Idealised.Token -> Bool
  keep (MkBounded t _ _) = case t of
      BlockComment _ => False
      LineComment  _ => False
      WS           _ => False
      _              => True

  export
  Lexer : Lexer Token
  Lexer = MkLexer Idealised.tokenMap (keep) EndInput

  export
  lexString : String -> Either LexError (List (WithBounds Token))
  lexString = lexString Lexer

  export
  lexFile : String -> IO $ Either LexFail (List (WithBounds Token))
  lexFile = lexFile Lexer

-- [ EOF ]
