module Circuits.Common.Lexer

import public Text.Lexer

import public Toolkit.Text.Lexer.Run

%default total

public export
record LangSpec where
  constructor W
  symbols : List String
  keywords : List String
  commentLine : String
  commentBlock : Pair String String
  docLine      : Maybe String
  docBlock     : Maybe (Pair String String)


public export
data Identifier = MkIdentifier String

export
Eq Identifier where
  (==) (MkIdentifier x) (MkIdentifier y) = x == y


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

showToken : Show a => String -> a -> String
showToken n a = "(" <+> n <+> " " <+> show a <+> ")"

export
Show Token where
  show (ID id)             = showToken "ID" id
  show (Keyword str)       = showToken "Keyword" str
  show (LineComment str)   = showToken "LineComment" str
  show (BlockComment str)  = showToken "BlockComment" str
  show (Documentation str) = showToken "Documentation" str

  show (LitNat n) = showToken "Nat" n

  show (Symbol s) = showToken "Symbol" s
  show (WS ws) = "WS"
  show (NotRecognised s) = showToken "Urgh" s
  show EndInput          = "EndInput"

identifier : Lexer
identifier = pred startIdent <+> many (pred validIdent)
  where
    startIdent : Char -> Bool
    startIdent x = isAlpha x

    validIdent : Char -> Bool
    validIdent '_' = True
    validIdent x = isAlphaNum x



tokenMap : LangSpec -> TokenMap Token
tokenMap (W symbols keywords comL (comBL, comBR) docLM docBM)
    = with List
        [
          (space, WS)
        , (lineComment (exact comL), LineComment)
        , (blockComment (exact comBL) (exact comBR), BlockComment)
        ]
        ++
          maybe [] (\dL => [(lineComment (exact dL), Documentation)])
                   docLM
        ++
          maybe [] (\dB
                     => [
                          (blockComment (exact (fst dB)) (exact (snd dB)), Documentation)
                        ])
                   docBM
        ++
        [
          (digits, \x => LitNat (integerToNat $ cast {to=Integer} x))
        ]
        ++
           map (\x => (exact x, Symbol)) symbols
        ++
        [
          (identifier, (\x => if elem x keywords then Keyword x else ID x))
        , (any, NotRecognised)
        ]

keep : WithBounds Token -> Bool
keep (MkBounded t _ _) = case t of
    BlockComment _ => False
    LineComment  _ => False
    WS           _ => False
    _              => True


namespace Circuits
  namespace Common

    export
    langSpec : List String -> List String -> LangSpec
    langSpec symbols keywords
      = W symbols
          keywords
          "//"
          ("/*", "*/")
          Nothing
          (Just ("/**", "**/"))

    export
    Lexer : LangSpec -> Lexer Token
    Lexer spec = MkLexer (Common.Lexer.tokenMap spec) (keep) EndInput

    export
    lexString : LangSpec -> String -> Either LexError (List (WithBounds Token))
    lexString spec = lexString (Lexer spec)

    export
    lexFile : LangSpec -> String -> IO $ Either LexFail (List (WithBounds Token))
    lexFile spec = lexFile (Lexer spec)

-- [ EOF ]
