|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Linear

import Data.List

import Test.Golden

%default covering

nonLinear : IO TestPool
nonLinear
  = testsInDir "linear"
               (const True)
               "Non-Linearly Wired NetList Tests"
               []
               Nothing


main : IO ()
main
  = runner [ !nonLinear ]


-- [ EOF ]
