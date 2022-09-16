|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Main

import Data.List

import Test.Golden

%default total

netlistGood : IO TestPool
netlistGood
  = testsInDir "netlist/good"
               (const True)
               "NetList Good library"
               Nil
               Nothing

covering
main : IO ()
main
  = runner [ !netlistGood ]

-- [ EOF ]
