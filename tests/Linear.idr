||| Borrowed From Idris2 and improved with Test.Unit
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
