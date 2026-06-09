module IRW.Core.HasNames

import public Data.Linear.Token
import public Data.Linear.Traverse1
import public IRW.Core.Name

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
  fullName : Bits32 -> F1 s FullName
  register : FullName -> F1 s Bits32

export %inline
resolveNames : Traversable1 f => Names s => f Bits32 -> F1 s (f FullName)
resolveNames = traverse1 fullName

export %inline
registerNames : Traversable1 f => Names s => f FullName -> F1 s (f Bits32)
registerNames = traverse1 register
