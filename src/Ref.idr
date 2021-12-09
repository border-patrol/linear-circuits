module Ref

import Toolkit.Data.Location

public export
record Ref where
  constructor MkRef
  span : FileContext
  get  : String

export
setSource : String -> Ref -> Ref
setSource new ref = record {span $= setSource new} ref

-- [ EOF ]
