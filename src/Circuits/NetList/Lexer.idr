|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Circuits.NetList.Lexer

import public Circuits.Common.Lexer

%default total

namespace NetList
  symbols : List String
  symbols = ["[", "]", ";", "{", "}", ":", ",", "=", "?", "(", ")", ".", "#", "!", "&", "|", "+"]

  keywords : List String
  keywords = [ "input", "output", "inout"
             , "module", "endmodule"
             , "wire"
             , "logic"
             , "and", "or", "xor", "nand", "nor", "xnor", "not"
             , "mux"
             , "assign"
             , "split", "collect"
             ]

  export
  Lexer : Lexer Token
  Lexer = Common.Lexer (langSpec symbols keywords)


-- [ EOF ]
