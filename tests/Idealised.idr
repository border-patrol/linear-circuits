|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
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
