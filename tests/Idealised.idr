||| Borrowed From Idris2 and improved with Test.Unit
module Idealised

import Data.List

import Test.Golden

%default total

tests : TestPool
tests
  = MkTestPool "Tests"
        []
        Nothing
        [
          "idealised"
        ]


covering
main : IO ()
main
  = runner [ tests ]

-- [ EOF ]
