||| Borrowed From Idris2 and improved with Test.Unit
module Netlist

import Data.List

import Test.Golden

%default covering

main : IO ()
main
  = runner [ !tests ]

  where
    tests : IO TestPool
    tests
      = testsInDir "netlist"
                   (const True)
                   "NetList Tests"
                   []
                   Nothing
-- [ EOF ]
