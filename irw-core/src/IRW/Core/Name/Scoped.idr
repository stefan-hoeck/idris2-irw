module IRW.Core.Name.Scoped

import Decidable.HDecEq
import public IRW.Core.Name
import public IRW.Libs.Data.SnocList.SizeOf
import public IRW.Libs.Data.SnocList.Thin

%default total

------------------------------------------------------------------------
-- Basic type definitions

||| Something which is having similar order as Scope itself
public export
0 Scopeable : (a: Type) -> Type
Scopeable = SnocList

||| A scope is represented by a list of names. E.g. in the following
||| rule, the scope Γ is extended with x when going under the λx.
||| binder:
|||
|||    Γ, x ⊢ t : B
|||  -----------------------------
|||    Γ    ⊢ λx. t : A → B
public export
0 Scope : Type
Scope = Scopeable Name

namespace Scope
  public export
  empty : Scopeable a
  empty = [<]

  public export %inline
  addInner : Scopeable a -> Scopeable a -> Scopeable a
  addInner = (++)

  public export %inline
  bind : Scopeable a -> a -> Scopeable a
  bind = (:<)

  public export
  single : a -> Scopeable a
  single n = [<n]

||| A scoped definition is one indexed by a scope
public export
0 Scoped : Type
Scoped = Scope -> Type

||| Deprecated: Use `hdecEq` instead
export %inline %deprecate
scopeEq : (sx, sy : Scope) -> Maybe0 (sx = sy)
scopeEq = hdecEq

export
mkFresh : Scope -> Name -> Name
mkFresh vs n =
  if n `elem` vs then assert_total $ mkFresh vs (next n) else n

--------------------------------------------------------------------------------
-- Compatible variables
--------------------------------------------------------------------------------

||| Proof that two `SnocList`s are of the same length
public export
data CompatibleVars : (sx, sy : SnocList a) -> Type where
   Pre : CompatibleVars sx sx
   Ext : CompatibleVars sx sy -> CompatibleVars (sx:<m) (sy:<n)

export
invertExt : CompatibleVars (sx:<m) (sy:<n) -> CompatibleVars sx sy
invertExt Pre = Pre
invertExt (Ext p) = p

export
extendCompats :
     (args : SnocList a)
  -> CompatibleVars sx sy
  -> CompatibleVars (sx ++ args) (sy ++ args)
extendCompats args    Pre = Pre
extendCompats [<]     prf = prf
extendCompats (sa:<a) prf = Ext $ extendCompats sa prf

export
decCompatibleVars : (sx, sy : SnocList a) -> Dec (CompatibleVars sx sy)
decCompatibleVars [<] [<]    = Yes Pre
decCompatibleVars [<] (_:<_) = No (\case p impossible)
decCompatibleVars (_:<_) [<] = No (\case p impossible)
decCompatibleVars (sx:<x) (sy:<y) = case decCompatibleVars sx sy of
  Yes prf => Yes (Ext prf)
  No nprf => No (nprf . invertExt)

export
areCompatibleVars : (sx, sy : SnocList a) -> Maybe (CompatibleVars sx sy)
areCompatibleVars [<]     [<]     = Just Pre
areCompatibleVars (sx:<_) (sy:<_) = Ext <$> areCompatibleVars sx sy
areCompatibleVars _       _       = Nothing

--------------------------------------------------------------------------------
-- Concepts
--------------------------------------------------------------------------------

||| Can append new variables to the scope of a scoped value.
public export
0 Weakenable : Scoped -> Type
Weakenable tm =
  {0 vars, ns : Scope} -> SizeOf ns -> tm vars -> tm (vars ++ ns)

||| Can remove variables to the scope of a scoped value.
public export
0 Strengthenable : Scoped -> Type
Strengthenable tm =
  {0 vars, ns : Scope} -> SizeOf ns -> tm (vars ++ ns) -> Maybe (tm vars)

public export
0 GenWeakenable : Scoped -> Type
GenWeakenable tm =
     {0 outer, ns, local : Scope}
  -> SizeOf local
  -> SizeOf ns
  -> tm (outer ++ local)
  -> tm ((outer ++ ns) ++ local)

public export
0 Thinnable : Scoped -> Type
Thinnable tm = {0 sx, sy : Scope} -> tm sx -> Thin sx sy -> tm sy

public export
0 Shrinkable : Scoped -> Type
Shrinkable tm = {0 sx, sy : Scope} -> tm sx -> Thin sy sx -> Maybe (tm sy)

public export
0 Embeddable : Scoped -> Type
Embeddable tm = {0 outer, vars : Scope} -> tm vars -> tm (outer++vars)

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

public export
interface Weaken (0 tm : Scoped) where
  constructor MkWeaken
  weaken : tm vars -> tm (vars:<nm)
  weakenNs : Weakenable tm
  -- default implementations
  weaken = weakenNs (suc zero)

-- This cannot be merged with Weaken because of WkCExp
public export
interface GenWeaken (0 tm : Scoped) where
  constructor MkGenWeaken
  genWeakenNs : GenWeakenable tm

export
genWeaken :
     {auto gw : GenWeaken tm}
  -> SizeOf local
  -> tm (outer++local)
  -> tm ((outer:<n)++local)
genWeaken l = genWeakenNs l (suc zero)

public export
interface Strengthen (0 tm : Scoped) where
  constructor MkStrengthen
  strengthenNs : Strengthenable tm

export
strengthen : Strengthen tm => tm (vars:<nm) -> Maybe (tm vars)
strengthen = strengthenNs (suc zero)

public export
interface FreelyEmbeddable (0 tm : Scoped) where
  constructor MkFreelyEmbeddable
  -- this is free for nameless representations
  embed : Embeddable tm
  embed = believe_me

export
FunctorFreelyEmbeddable : Functor f => FreelyEmbeddable tm => FreelyEmbeddable (f . tm)
FunctorFreelyEmbeddable = MkFreelyEmbeddable believe_me

export
ListFreelyEmbeddable : FreelyEmbeddable tm => FreelyEmbeddable (List . tm)
ListFreelyEmbeddable = FunctorFreelyEmbeddable

export
MaybeFreelyEmbeddable : FreelyEmbeddable tm => FreelyEmbeddable (Maybe . tm)
MaybeFreelyEmbeddable = FunctorFreelyEmbeddable

export
GenWeakenWeakens : GenWeaken tm => Weaken tm
GenWeakenWeakens = MkWeaken (genWeaken zero) (genWeakenNs zero)

export
FunctorGenWeaken : Functor f => GenWeaken tm => GenWeaken (f . tm)
FunctorGenWeaken = MkGenWeaken (\ l, s => map (genWeakenNs l s))

export
FunctorWeaken : Functor f => Weaken tm => Weaken (f . tm)
FunctorWeaken = MkWeaken (go (suc zero)) go where

  go : Weakenable (f . tm)
  go s = map (weakenNs s)

export
ListWeaken : Weaken tm => Weaken (List . tm)
ListWeaken = FunctorWeaken

export
MaybeWeaken : Weaken tm => Weaken (Maybe . tm)
MaybeWeaken = FunctorWeaken

public export
interface Weaken tm => IsScoped (0 tm : Scoped) where
  compatNs : CompatibleVars sx sy -> tm sx -> tm sy

  thin : Thinnable tm
  shrink : Shrinkable tm

export
compat : IsScoped tm => tm (sx:<m) -> tm (sx:<n)
compat = compatNs (Ext Pre)
