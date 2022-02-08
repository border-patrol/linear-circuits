||| Borrowed From Idris2 and improved with Test.Unit
module Netlist

import Data.List

import Test.Golden

%default total

dump : TestPool
dump
  = MkTestPool "Dump"
        []
        Nothing
        [
          "netlist-common-good"
        ]

tests : TestPool
tests
  = MkTestPool "Tests"
        []
        Nothing
        [
          "netlist-linear-good-001"
        , "netlist-linear-good-002"

        , "netlist-linear-bad-001"
        , "netlist-linear-bad-002"

        , "netlist-datatype-001"
        ]


covering
main : IO ()
main
  = runner [ tests, dump ]

-- [ EOF ]
