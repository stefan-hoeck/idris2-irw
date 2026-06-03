module IRW.Core.TT.Term

import Derive.Prelude
import IRW.Algebra

import IRW.Core.FC

import IRW.Core.Name.Scoped
import IRW.Core.TT.Binder
import IRW.Core.TT.Primitive
import IRW.Core.TT.Var

import Data.List
import Data.String

import IRW.Libs.Data.SizeOf

%default total
%language ElabReflection
%hide Language.Reflection.TT.Constant
%hide Language.Reflection.TT.FC
%hide Language.Reflection.TT.IsVar
%hide Language.Reflection.TT.LazyReason
%hide Language.Reflection.TT.Name
%hide Language.Reflection.TT.Namespace
%hide Language.Reflection.TT.NameType
%hide Language.Reflection.TT.PiInfo
%hide Language.Reflection.TTImp.UseSide

--------------------------------------------------------------------------------
-- Name Types
--------------------------------------------------------------------------------

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Bits32) -> (arity : Nat) -> NameType
     TyCon   : (arity : Nat) -> NameType

%runElab derive "NameType" [Show,Eq]

%name NameType nt

export
isCon : NameType -> Maybe Nat
isCon (DataCon t a) = Just a
isCon (TyCon a) = Just a
isCon _ = Nothing

--------------------------------------------------------------------------------
-- Type-checked Terms
--------------------------------------------------------------------------------

public export
data LazyReason = LInf | LLazy | LUnknown

%runElab derive "LazyReason" [Show,Eq,Ord]

%name LazyReason lz

||| For as patterns matching linear arguments, select which side is
||| consumed
public export
data UseSide = UseLeft | UseRight

%runElab derive "UseSide" [Show,Eq,Ord]

%name UseSide side

public export
data WhyErased a = Placeholder | Impossible | Dotted a

%runElab derive "WhyErased" [Show,Eq,Ord]

export
Interpolation a => Interpolation (WhyErased a) where
  interpolate Placeholder = "placeholder"
  interpolate Impossible = "impossible"
  interpolate (Dotted x) = "dotted \{x}"

%name WhyErased why

export %tcinline
mapWhy : (a -> b) -> WhyErased a -> WhyErased b
mapWhy f Placeholder = Placeholder
mapWhy f Impossible = Impossible
mapWhy f (Dotted x) = Dotted (f x)

export %inline
Functor WhyErased where map = mapWhy

export
Foldable WhyErased where
  foldr c n (Dotted x) = c x n
  foldr c n _ = n

export
Traversable WhyErased where
  traverse f Placeholder = pure Placeholder
  traverse f Impossible = pure Impossible
  traverse f (Dotted x) = Dotted <$> f x

--------------------------------------------------------------------------------
-- Core Terms
--------------------------------------------------------------------------------

public export
data Term : Scope -> Type where
     Local : FC -> (isLet : Maybe Bool) -> Var vs -> Term vs
     Ref : FC -> NameType -> (name : Name) -> Term vs
     -- Metavariables and the scope they are applied to
     Meta : FC -> Name -> Bits32 -> List (Term vs) -> Term vs
     Bind : FC -> (x : Name) ->
            (b : Binder (Term vs)) ->
            (scope : Term (Scope.bind vs x)) -> Term vs
     App : FC -> (fn : Term vs) -> (arg : Term vs) -> Term vs
     -- as patterns; since we check LHS patterns as terms before turning
     -- them into patterns, this helps us get it right. When normalising,
     -- we just reduce the inner term and ignore the 'as' part
     -- The 'as' part should really be a Name rather than a Term, but it's
     -- easier this way since it gives us the ability to work with unresolved
     -- names (Ref) and resolved names (Local) without having to define a
     -- special purpose thing. (But it'd be nice to tidy that up, nevertheless)
     As : FC -> UseSide -> (as : Term vs) -> (pat : Term vs) -> Term vs
     -- Typed laziness annotations
     TDelayed : FC -> LazyReason -> Term vs -> Term vs
     TDelay : FC -> LazyReason -> (ty : Term vs) -> (arg : Term vs) -> Term vs
     TForce : FC -> LazyReason -> Term vs -> Term vs
     PrimVal : FC -> (c : Constant) -> Term vs
     Erased : FC -> WhyErased (Term vs) -> Term vs
     TType : FC -> Name -> -- universe variable
             Term vs

%runElab deriveIndexed "Term" [Show]
%name Term t, u

public export
ClosedTerm : Type
ClosedTerm = Term [<]

--------------------------------------------------------------------------------
-- Weakening
--------------------------------------------------------------------------------

insL : GenWeakenable (List . Term)

insB : GenWeakenable (Binder . Term)

insW : GenWeakenable (WhyErased . Term)

insP : GenWeakenable (PiInfo . Term)

insT : GenWeakenable Term
insT o ns (Local fc r v)      = Local fc r $ genWeakenNs o ns v
insT o ns (Ref fc nt name)    = Ref fc nt name
insT o ns (Meta fc n m ts)    = Meta fc n m (insL o ns ts)
insT o ns (Bind fc x b sc)    = Bind fc x (insB o ns b) (insT (suc o) ns sc)
insT o ns (App fc fn x)       = App fc (insT o ns fn) (insT o ns x)
insT o ns (As fc s as pat)    = As fc s (insT o ns as) (insT o ns pat)
insT o ns (TDelayed fc lz t)  = TDelayed fc lz (insT o ns t)
insT o ns (TDelay fc lz ty x) = TDelay fc lz (insT o ns ty) (insT o ns x)
insT o ns (TForce fc lz t)    = TForce fc lz (insT o ns t)
insT o ns (PrimVal fc c)      = PrimVal fc c
insT o ns (Erased fc why)     = Erased fc (insW o ns why)
insT o ns (TType fc n)        = TType fc n

insL o ns []      = []
insL o ns (t::ts) = insT o ns t :: insL o ns ts

insW o n Placeholder = Placeholder
insW o n Impossible = Impossible
insW o n (Dotted x) = Dotted $ insT o n x

insP o n Implicit = Implicit
insP o n Explicit = Explicit
insP o n AutoImplicit = AutoImplicit
insP o n (DefImplicit x) = DefImplicit (insT o n x)

insB o n (Lam fc r p t) = Lam fc r (insP o n p) (insT o n t)
insB o n (Let fc r v t) = Let fc r (insT o n v) (insT o n t)
insB o n (Pi fc r p t) = Pi fc r (insP o n p) (insT o n t)
insB o n (PVar fc r p t) = PVar fc r (insP o n p) (insT o n t)
insB o n (PLet fc r v t) = PLet fc r (insT o n v) (insT o n t)
insB o n (PVTy fc r t) = PVTy fc r (insT o n t)

export %inline
GenWeaken Term where genWeakenNs = insT

export %inline
GenWeaken (PiInfo . Term) where genWeakenNs = insP

export %inline
GenWeaken (WhyErased . Term) where genWeakenNs = insW

export %inline
GenWeaken (Binder . Term) where genWeakenNs = insB

export %inline
GenWeaken (List . Term) where genWeakenNs = insL

export
compatTerm : CompatibleVars xs ys -> Term xs -> Term ys
compatTerm compat tm = believe_me tm -- no names in term, so it's identity
-- This is how we would define it:
-- compatTerm CompatPre tm = tm
-- compatTerm prf (Local fc r idx vprf)
--     = let MkVar vprf' = compatIsVar prf vprf in
--           Local fc r _ vprf'
-- compatTerm prf (Ref fc x name) = Ref fc x name
-- compatTerm prf (Meta fc n i args)
--     = Meta fc n i (map (compatTerm prf) args)
-- compatTerm prf (Bind fc x b scope)
--     = Bind fc x (map (compatTerm prf) b) (compatTerm (CompatExt prf) scope)
-- compatTerm prf (App fc fn arg)
--     = App fc (compatTerm prf fn) (compatTerm prf arg)
-- compatTerm prf (As fc s as tm)
--     = As fc s (compatTerm prf as) (compatTerm prf tm)
-- compatTerm prf (TDelayed fc r ty) = TDelayed fc r (compatTerm prf ty)
-- compatTerm prf (TDelay fc r ty tm)
--     = TDelay fc r (compatTerm prf ty) (compatTerm prf tm)
-- compatTerm prf (TForce fc r x) = TForce fc r (compatTerm prf x)
-- compatTerm prf (PrimVal fc c) = PrimVal fc c
-- compatTerm prf (Erased fc i) = Erased fc i
-- compatTerm prf (TType fc) = TType fc
--

--------------------------------------------------------------------------------
-- Shrinking
--------------------------------------------------------------------------------

shrL : Shrinkable (List . Term)

shrB : Shrinkable (Binder . Term)

shrW : Shrinkable (WhyErased . Term)

shrP : Shrinkable (PiInfo . Term)

shrT : Shrinkable Term
shrT (Local fc r v) th      = Local fc r <$> shrink v th
shrT (Ref fc nt name) th    = Just $ Ref fc nt name
shrT (Meta fc n m ts) th    = Meta fc n m <$> shrL ts th
shrT (Bind fc x b sc) th    = Bind fc x  <$> shrB b th <*> shrT sc (Keep th)
shrT (App fc fn x) th       = App fc <$> shrT fn th <*> shrT x th
shrT (As fc s as pat) th    = As fc s <$> shrT as th <*> shrT pat th
shrT (TDelayed fc lz t) th  = TDelayed fc lz <$> shrT t th
shrT (TDelay fc lz ty x) th = TDelay fc lz <$> shrT ty th <*> shrT x th
shrT (TForce fc lz t) th    = TForce fc lz <$> shrT t th
shrT (PrimVal fc c) th      = Just $ PrimVal fc c
shrT (Erased fc why) th     = Erased fc <$> shrW why th
shrT (TType fc n) th        = Just $ TType fc n

shrL []      th = Just []
shrL (t::ts) th = [| shrT t th :: shrL ts th |]

shrW Placeholder th = Just Placeholder
shrW Impossible  th = Just Impossible
shrW (Dotted x)  th = Dotted <$> shrT x th

shrP Implicit        th = Just Implicit
shrP Explicit        th = Just Explicit
shrP AutoImplicit    th = Just AutoImplicit
shrP (DefImplicit x) th = DefImplicit <$> shrT x th

shrB (Lam fc r p t)  th = Lam fc r  <$> shrP p th <*> shrT t th
shrB (Let fc r v t)  th = Let fc r  <$> shrT v th <*> shrT t th
shrB (Pi fc r p t)   th = Pi fc r   <$> shrP p th <*> shrT t th
shrB (PVar fc r p t) th = PVar fc r <$> shrP p th <*> shrT t th
shrB (PLet fc r v t) th = PLet fc r <$> shrT v th <*> shrT t th
shrB (PVTy fc r t)   th = PVTy fc r <$> shrT t th

--------------------------------------------------------------------------------
-- Thinning
--------------------------------------------------------------------------------

thiL : Thinnable (List . Term)

thiB : Thinnable (Binder . Term)

thiW : Thinnable (WhyErased . Term)

thiP : Thinnable (PiInfo . Term)

thiT : Thinnable Term
thiT (Local fc r v) th      = Local fc r $ thin v th
thiT (Ref fc nt name) th    = Ref fc nt name
thiT (Meta fc n m ts) th    = Meta fc n m $ thiL ts th
thiT (Bind fc x b sc) th    = Bind fc x  (thiB b th) (thiT sc (Keep th))
thiT (App fc fn x) th       = App fc (thiT fn th) (thiT x th)
thiT (As fc s as pat) th    = As fc s (thiT as th) (thiT pat th)
thiT (TDelayed fc lz t) th  = TDelayed fc lz $ thiT t th
thiT (TDelay fc lz ty x) th = TDelay fc lz (thiT ty th) (thiT x th)
thiT (TForce fc lz t) th    = TForce fc lz $ thiT t th
thiT (PrimVal fc c) th      = PrimVal fc c
thiT (Erased fc why) th     = Erased fc $ thiW why th
thiT (TType fc n) th        = TType fc n

thiL []      th = []
thiL (t::ts) th = thiT t th :: thiL ts th

thiW Placeholder th = Placeholder
thiW Impossible  th = Impossible
thiW (Dotted x)  th = Dotted $ thiT x th

thiP Implicit        th = Implicit
thiP Explicit        th = Explicit
thiP AutoImplicit    th = AutoImplicit
thiP (DefImplicit x) th = DefImplicit $ thiT x th

thiB (Lam fc r p t)  th = Lam fc r  (thiP p th) (thiT t th)
thiB (Let fc r v t)  th = Let fc r  (thiT v th) (thiT t th)
thiB (Pi fc r p t)   th = Pi fc r   (thiP p th) (thiT t th)
thiB (PVar fc r p t) th = PVar fc r (thiP p th) (thiT t th)
thiB (PLet fc r v t) th = PLet fc r (thiT v th) (thiT t th)
thiB (PVTy fc r t)   th = PVTy fc r (thiT t th)

export
FreelyEmbeddable Term where

export %inline
IsScoped Term where
  shrink = shrT
  thin = thiT
  compatNs x = believe_me x

export %inline
IsScoped (List . Term) where
  shrink = shrL
  thin = thiL
  compatNs x = believe_me x

export %inline
IsScoped (Binder . Term) where
  shrink = shrB
  thin = thiB
  compatNs x = believe_me x

export %inline
IsScoped (PiInfo . Term) where
  shrink = shrP
  thin = thiP
  compatNs x = believe_me x

export %inline
IsScoped (WhyErased . Term) where
  shrink = shrW
  thin = thiW
  compatNs x = believe_me x

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

export
apply : FC -> Term vs -> List (Term vs) -> Term vs
apply loc fn [] = fn
apply loc fn (a :: args) = apply loc (App loc fn a) args

||| Creates a chain of `App` nodes, each with its own file context
export
applySpineWithFC : Term vs -> SnocList (FC, Term vs) -> Term vs
applySpineWithFC fn [<] = fn
applySpineWithFC fn (args :< (fc, arg)) = App fc (applySpineWithFC fn args) arg

||| Creates a chain of `App` nodes, each with its own file context
export
applyStackWithFC : Term vs -> List (FC, Term vs) -> Term vs
applyStackWithFC fn [] = fn
applyStackWithFC fn ((fc, arg) :: args) = applyStackWithFC (App fc fn arg) args

||| Build a simple function type
export
fnType : FC -> Term vs -> Term vs -> Term vs
fnType fc arg scope =
  Bind EmptyFC (MN "_" 0) (Pi fc top Explicit arg) (weaken scope)

||| Build a simple linear function type
export
linFnType : FC -> Term vs -> Term vs -> Term vs
linFnType fc arg scope =
  Bind EmptyFC (MN "_" 0) (Pi fc linear Explicit arg) (weaken scope)

export
getFnArgs : Term vs -> (Term vs, List (Term vs))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vs) -> Term vs -> (Term vs, List (Term vs))
    getFA args (App _ f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
getFn : Term vs -> Term vs
getFn (App _ f a) = getFn f
getFn tm = tm

export %inline
getArgs : Term vs -> List (Term vs)
getArgs = snd . getFnArgs

--------------------------------------------------------------------------------
-- Namespace manipulations
--------------------------------------------------------------------------------

||| Remove/restore the given namespace from all Refs. This is to allow
||| writing terms and case trees to disk without repeating the same namespace
||| all over the place.
public export
interface StripNamespace a where
  trimNS : Namespace -> a -> a
  restoreNS : Namespace -> a -> a

export
StripNamespace Name where
  trimNS ns nm@(NS tns n) = if ns == tns then NS emptyNS n else nm
    -- ^ A blank namespace, rather than a UN, so we don't catch primitive
    -- names which are represented as UN.
  trimNS ns nm = nm

  restoreNS ns nm@(NS tns n) =
    case tns.names of
      [<] => NS ns n
      _   => nm
  restoreNS ns nm = nm

adjL : (Name -> Name) -> List (Term vs) -> List (Term vs)

adjB : (Name -> Name) -> Binder (Term vs) -> Binder (Term vs)

adjW : (Name -> Name) -> WhyErased (Term vs) -> WhyErased (Term vs)

adjP : (Name -> Name) -> PiInfo (Term vs) -> PiInfo (Term vs)

adjT : (Name -> Name) -> Term vs -> Term vs
adjT f (Ref fc nt name)    = Ref fc nt (f name)
adjT f (Meta fc n m ts)    = Meta fc n m $ adjL f ts
adjT f (Bind fc x b sc)    = Bind fc x  (adjB f b) (adjT f sc)
adjT f (App fc fn x)       = App fc (adjT f fn) (adjT f x)
adjT f (As fc s as pat)    = As fc s (adjT f as) (adjT f pat)
adjT f (TDelayed fc lz t)  = TDelayed fc lz $ adjT f t
adjT f (TDelay fc lz ty x) = TDelay fc lz (adjT f ty) (adjT f x)
adjT f (TForce fc lz t)    = TForce fc lz $ adjT f t
adjT f x                   = x

adjL f []      = []
adjL f (t::ts) = adjT f t :: adjL f ts

adjW f (Dotted x) = Dotted $ adjT f x
adjW f x          = x

adjP f (DefImplicit x) = DefImplicit $ adjT f x
adjP f x               = x

adjB f (Lam fc r p t)  = Lam fc r  (adjP f p) (adjT f t)
adjB f (Let fc r v t)  = Let fc r  (adjT f v) (adjT f t)
adjB f (Pi fc r p t)   = Pi fc r   (adjP f p) (adjT f t)
adjB f (PVar fc r p t) = PVar fc r (adjP f p) (adjT f t)
adjB f (PLet fc r v t) = PLet fc r (adjT f v) (adjT f t)
adjB f (PVTy fc r t)   = PVTy fc r (adjT f t)

export %inline
StripNamespace (Term vs) where
  trimNS = adjT . trimNS
  restoreNS = adjT . restoreNS

export
isErased : Term vs -> Bool
isErased (Erased {}) = True
isErased _ = False

export
getLoc : Term vs -> FC
getLoc (Local fc _ _) = fc
getLoc (Ref fc _ _) = fc
getLoc (Meta fc _ _ _) = fc
getLoc (Bind fc _ _ _) = fc
getLoc (App fc _ _) = fc
getLoc (As fc _ _ _) = fc
getLoc (TDelayed fc _ _) = fc
getLoc (TDelay fc _ _ _) = fc
getLoc (TForce fc _ _) = fc
getLoc (PrimVal fc _) = fc
getLoc (Erased fc i) = fc
getLoc (TType fc _) = fc

export
compatible : LazyReason -> LazyReason -> Bool
compatible LUnknown _ = True
compatible _ LUnknown = True
compatible x y = x == y

export
eqWhyErasedBy : (a -> b -> Bool) -> WhyErased a -> WhyErased b -> Bool
eqWhyErasedBy eq Impossible Impossible = True
eqWhyErasedBy eq Placeholder Placeholder = True
eqWhyErasedBy eq (Dotted t) (Dotted u) = eq t u
eqWhyErasedBy eq _ _ = False

export total
eqTerm : Term vs -> Term vs' -> Bool
eqTerm (Local _ _ v) (Local _ _ v') = varIdx v == varIdx v'
eqTerm (Ref _ _ n) (Ref _ _ n') = n == n'
eqTerm (Meta _ _ i args) (Meta _ _ i' args')
    = i == i' && assert_total (all (uncurry eqTerm) (zip args args'))
eqTerm (Bind _ _ b sc) (Bind _ _ b' sc')
    = assert_total (eqBinderBy eqTerm b b') && eqTerm sc sc'
eqTerm (App _ f a) (App _ f' a') = eqTerm f f' && eqTerm a a'
eqTerm (As _ _ a p) (As _ _ a' p') = eqTerm a a' && eqTerm p p'
eqTerm (TDelayed _ _ t) (TDelayed _ _ t') = eqTerm t t'
eqTerm (TDelay _ _ t x) (TDelay _ _ t' x') = eqTerm t t' && eqTerm x x'
eqTerm (TForce _ _ t) (TForce _ _ t') = eqTerm t t'
eqTerm (PrimVal _ c) (PrimVal _ c') = c == c'
eqTerm (Erased _ i) (Erased _ i') = assert_total (eqWhyErasedBy eqTerm i i')
eqTerm (TType {}) (TType {}) = True
eqTerm _ _ = False

export %inline
Eq (Term vs) where (==) = eqTerm

--------------------------------------------------------------------------------
-- Scope checking
--------------------------------------------------------------------------------

rsvL : (vs : Scope) -> List (Term vs) -> List (Term vs)

rsvB : (vs : Scope) -> Binder (Term vs) -> Binder (Term vs)

rsvW : (vs : Scope) -> WhyErased (Term vs) -> WhyErased (Term vs)

rsvP : (vs : Scope) -> PiInfo (Term vs) -> PiInfo (Term vs)

rsvT : (vs : Scope) -> Term vs -> Term vs
rsvT vs (Ref fc Bound name)    =
  case isNVar name vs of
    Nothing => Ref fc Bound name
    Just x  => Local fc (Just False) (forgetName x)
rsvT vs (Meta fc n m ts)    = Meta fc n m $ rsvL vs ts
rsvT vs (Bind fc x b sc)    = Bind fc x  (rsvB vs b) (rsvT (vs:<x) sc)
rsvT vs (App fc fn x)       = App fc (rsvT vs fn) (rsvT vs x)
rsvT vs (As fc s as pat)    = As fc s (rsvT vs as) (rsvT vs pat)
rsvT vs (TDelayed fc lz t)  = TDelayed fc lz $ rsvT vs t
rsvT vs (TDelay fc lz ty x) = TDelay fc lz (rsvT vs ty) (rsvT vs x)
rsvT vs (TForce fc lz t)    = TForce fc lz $ rsvT vs t
rsvT vs x                   = x

rsvL vs []      = []
rsvL vs (t::ts) = rsvT vs t :: rsvL vs ts

rsvW vs (Dotted x) = Dotted $ rsvT vs x
rsvW vs x          = x

rsvP vs (DefImplicit x) = DefImplicit $ rsvT vs x
rsvP vs x               = x

rsvB vs (Lam fc r p t)  = Lam fc r  (rsvP vs p) (rsvT vs t)
rsvB vs (Let fc r v t)  = Let fc r  (rsvT vs v) (rsvT vs t)
rsvB vs (Pi fc r p t)   = Pi fc r   (rsvP vs p) (rsvT vs t)
rsvB vs (PVar fc r p t) = PVar fc r (rsvP vs p) (rsvT vs t)
rsvB vs (PLet fc r v t) = PLet fc r (rsvT vs v) (rsvT vs t)
rsvB vs (PVTy fc r t)   = PVTy fc r (rsvT vs t)

||| Replace any Ref Bound in a type with appropriate local
export %inline
resolveNames : (vs : Scope) -> Term vs -> Term vs
resolveNames = rsvT
