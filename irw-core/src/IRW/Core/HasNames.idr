module IRW.Core.HasNames

import Data.Linear.Traverse1
import public IRW.Core.Name
import public Data.Linear.Token

%default total

||| Environment for resolving names: Converts fully qualified
||| names to their index (for fast array lookup) and convert
||| resolved indices back to the fully qualified name.
|||
||| Note: All of this is part of the global `Context` in Idris,
|||       which we are trying to disentangle and split into smaller
|||       interfaces here.
public export
interface Names (0 s : Type) where
  constructor MkNames
  fullName : Bits32 -> F1 s (Maybe FullName)
  register : FullName -> F1 s Bits32
