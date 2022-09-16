|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.Idealised.Lexer

import public Circuits.Common.Lexer

%default total

namespace Idealised

  symbols : List String
  symbols = ["[", "]", ";", "{", "}", ":", ",", "=", "?", "(", ")", ".", "#", "!", "&", "|", "+"]


  keywords : List String
  keywords = [ "input", "output"
             , "module", "endmodule"
             , "wire"
             , "logic", "as", "in"
             , "and", "ior", "xor", "nand", "nior", "xnor", "not"
             , "copy", "join"
             , "extract", "insert"
             , "first", "last"
             , "index", "merge"
             , "mux"
             ]

  export
  Lexer : Lexer Token
  Lexer = Common.Lexer (langSpec symbols keywords)


-- [ EOF ]
