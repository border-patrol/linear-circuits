module Ref

import Toolkit.Data.Location

public export
record Ref where
  constructor MkRef
  span : FileContext
  get  : String

-- [ EOF ]
