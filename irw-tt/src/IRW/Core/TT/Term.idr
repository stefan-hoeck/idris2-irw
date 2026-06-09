module IRW.Core.TT.Term

import Derive.Prelude
import IRW.Algebra

import IRW.Core.FC

import IRW.Core.Name.Scoped
import IRW.Core.HasNames
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

export
Foldable1 WhyErased where
  foldl1 f v (Dotted x) t = f v x t
  foldl1 f v _ t = v # t

export
Traversable1 WhyErased where
  traverse1 f Placeholder t = Placeholder # t
  traverse1 f Impossible t = Impossible # t
  traverse1 f (Dotted x) t = let y # t := f x t in Dotted y # t

export
Functor WhyErased where
  map f p = run1 $ traverse1 (\x,t => f x # t) p

export
Foldable WhyErased where
  foldr f acc p = run1 $ foldr1 (\x,y,t => f x y # t) acc p
  foldl f acc p = run1 $ foldl1 (\x,y,t => f x y # t) acc p
  foldMap f p = run1 $ foldMap1 (\x,t => f x # t) p

--------------------------------------------------------------------------------
-- Core Terms
--------------------------------------------------------------------------------

public export
data Term : (n : Type) -> Scope -> Type where
     Local : FC -> (isLet : Maybe Bool) -> Var vs -> Term n vs
     Ref : FC -> NameType -> (name : n) -> Term n vs
     -- Metavariables and the scope they are applied to
     Meta : FC -> VarName -> List (Term n vs) -> Term n vs
     Bind : FC -> (x : VarName) ->
            (b : Binder (Term n vs)) ->
            (scope : Term n (Scope.bind vs x)) -> Term n vs
     App : FC -> (fn : Term n vs) -> (arg : Term n vs) -> Term n vs
     -- as patterns; since we check LHS patterns as terms before turning
     -- them into patterns, this helps us get it right. When normalising,
     -- we just reduce the inner term and ignore the 'as' part
     -- The 'as' part should really be a Name rather than a Term, but it's
     -- easier this way since it gives us the ability to work with unresolved
     -- names (Ref) and resolved names (Local) without having to define a
     -- special purpose thing. (But it'd be nice to tidy that up, nevertheless)
     As : FC -> UseSide -> (as : Term n vs) -> (pat : Term n vs) -> Term n vs
     -- Typed laziness annotations
     TDelayed : FC -> LazyReason -> Term n vs -> Term n vs
     TDelay : FC -> LazyReason -> (ty : Term n vs) -> (arg : Term n vs) -> Term n vs
     TForce : FC -> LazyReason -> Term n vs -> Term n vs
     PrimVal : FC -> (c : Constant) -> Term n vs
     Erased : FC -> WhyErased (Term n vs) -> Term n vs
     TType : FC -> VarName -> -- universe variable
             Term n vs

%runElab derivePattern "Term" [P,I] [Show]
%name Term t, u

public export
0 FTerm : Scoped
FTerm = Term FullName

public export
0 ClosedTerm : Type
ClosedTerm = Term FullName [<]

public export
record NTerm (sc : Scope) (n : Type) where
  constructor NT
  term : Term n sc

covering
foldT : (a -> n -> F1 s a) -> a -> Term n vs -> F1 s a
foldT f x (Local fc isLet y) t = x # t
foldT f x (Ref fc nt name) t = f x name t
foldT f x (Meta fc y ts) t = Traverse1.foldl1 (foldT f) x ts t
foldT f x (Bind fc y b scope) t =
 let x2 # t := Traverse1.foldl1 (foldT f) x b t in foldT f x2 scope t
foldT f x (App fc fn arg) t =
 let x2 # t := foldT f x fn t in foldT f x2 arg t
foldT f x (As fc side as pat) t =
 let x2 # t := foldT f x as t in foldT f x2 pat t
foldT f x (TDelayed fc lz u) t = foldT f x u t
foldT f x (TDelay fc lz ty arg) t =
 let x2 # t := foldT f x ty t in foldT f x2 arg t
foldT f x (TForce fc lz u) t = foldT f x u t
foldT f x (PrimVal fc c) t = x # t
foldT f x (Erased fc why) t = foldl1 (foldT f) x why t
foldT f x (TType fc y) t = x # t

covering
travT : (a -> F1 s b) -> Term a vs -> F1 s (Term b vs)
travT f (Local fc isLet y) t = Local fc isLet y # t
travT f (Ref fc nt name) t =
 let n2 # t := f name t
  in Ref fc nt n2 # t
travT f (Meta fc y ts) t =
 let ts2 # t := traverse1 (travT f) ts t
  in Meta fc y ts2 # t
travT f (Bind fc y b scope) t =
 let b2 # t := traverse1 (travT f) b t
     s2 # t := travT f scope t
  in Bind fc y b2 s2 # t
travT f (App fc fn arg) t =
 let f2 # t := travT f fn t
     a2 # t := travT f arg t
  in App fc f2 a2 # t
travT f (As fc side as pat) t =
 let a2 # t := travT f as t
     p2 # t := travT f pat t
  in As fc side a2 p2 # t
travT f (TDelayed fc lz u) t =
 let u2 # t := travT f u t
  in TDelayed fc lz u2 # t
travT f (TDelay fc lz ty arg) t =
 let t2 # t := travT f ty t
     a2 # t := travT f arg t
  in TDelay fc lz t2 a2 # t
travT f (TForce fc lz u) t =
 let u2 # t := travT f u t
  in TForce fc lz u2 # t
travT f (PrimVal fc c) t = PrimVal fc c # t
travT f (Erased fc why) t =
 let w2 # t := traverse1 (travT f) why t
  in Erased fc w2 # t
travT f (TType fc y) t = TType fc y # t

export
Foldable1 (NTerm vs) where
  foldl1 f v (NT tt) t = assert_total $ foldT f v tt t

export
Traversable1 (NTerm vs) where
  traverse1 f (NT tt) t =
   let t2 # t := assert_total $ travT f tt t
    in NT t2 # t

export
Functor (NTerm vs) where
  map f p = run1 $ traverse1 (\x,t => f x # t) p

export
Foldable (NTerm vs) where
  foldr f acc p = run1 $ foldr1 (\x,y,t => f x y # t) acc p
  foldl f acc p = run1 $ foldl1 (\x,y,t => f x y # t) acc p
  foldMap f p = run1 $ foldMap1 (\x,t => f x # t) p

--------------------------------------------------------------------------------
-- Weakening
--------------------------------------------------------------------------------

insL : GenWeakenable (List . Term n)

insB : GenWeakenable (Binder . Term n)

insW : GenWeakenable (WhyErased . Term n)

insP : GenWeakenable (PiInfo . Term n)

insT : GenWeakenable (Term n)
insT o ns (Local fc r v)      = Local fc r $ genWeakenNs o ns v
insT o ns (Ref fc nt name)    = Ref fc nt name
insT o ns (Meta fc n ts)      = Meta fc n (insL o ns ts)
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
GenWeaken (Term n) where genWeakenNs = insT

export %inline
GenWeaken (PiInfo . Term n) where genWeakenNs = insP

export %inline
GenWeaken (WhyErased . Term n) where genWeakenNs = insW

export %inline
GenWeaken (Binder . Term n) where genWeakenNs = insB

export %inline
GenWeaken (List . Term n) where genWeakenNs = insL

export
compatTerm : CompatibleVars xs ys -> Term n xs -> Term n ys
compatTerm compat tm = believe_me tm -- no names in term, so it's identity

--------------------------------------------------------------------------------
-- Shrinking
--------------------------------------------------------------------------------

shrL : Shrinkable (List . Term n)

shrB : Shrinkable (Binder . Term n)

shrW : Shrinkable (WhyErased . Term n)

shrP : Shrinkable (PiInfo . Term n)

shrT : Shrinkable (Term n)
shrT (Local fc r v) th      = Local fc r <$> shrink v th
shrT (Ref fc nt name) th    = Just $ Ref fc nt name
shrT (Meta fc n ts) th      = Meta fc n <$> shrL ts th
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

thiL : Thinnable (List . Term n)

thiB : Thinnable (Binder . Term n)

thiW : Thinnable (WhyErased . Term n)

thiP : Thinnable (PiInfo . Term n)

thiT : Thinnable (Term n)
thiT (Local fc r v) th      = Local fc r $ thin v th
thiT (Ref fc nt name) th    = Ref fc nt name
thiT (Meta fc n ts) th      = Meta fc n $ thiL ts th
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
FreelyEmbeddable (Term n) where

export %inline
IsScoped (Term n) where
  shrink = shrT
  thin = thiT
  compatNs x = believe_me x

export %inline
IsScoped (List . Term n) where
  shrink = shrL
  thin = thiL
  compatNs x = believe_me x

export %inline
IsScoped (Binder . Term n) where
  shrink = shrB
  thin = thiB
  compatNs x = believe_me x

export %inline
IsScoped (PiInfo . Term n) where
  shrink = shrP
  thin = thiP
  compatNs x = believe_me x

export %inline
IsScoped (WhyErased . Term n) where
  shrink = shrW
  thin = thiW
  compatNs x = believe_me x

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

export
apply : FC -> Term n vs -> List (Term n vs) -> Term n vs
apply loc fn [] = fn
apply loc fn (a :: args) = apply loc (App loc fn a) args

||| Creates a chain of `App` nodes, each with its own file context
export
applySpineWithFC : Term n vs -> SnocList (FC, Term n vs) -> Term n vs
applySpineWithFC fn [<] = fn
applySpineWithFC fn (args :< (fc, arg)) = App fc (applySpineWithFC fn args) arg

||| Creates a chain of `App` nodes, each with its own file context
export
applyStackWithFC : Term n vs -> List (FC, Term n vs) -> Term n vs
applyStackWithFC fn [] = fn
applyStackWithFC fn ((fc, arg) :: args) = applyStackWithFC (App fc fn arg) args

fnName : VarName
fnName = "_0"

||| Build a simple function type
export
fnType : FC -> Term n vs -> Term n vs -> Term n vs
fnType fc arg scope =
  Bind EmptyFC fnName (Pi fc top Explicit arg) (weaken scope)

||| Build a simple linear function type
export
linFnType : FC -> Term n vs -> Term n vs -> Term n vs
linFnType fc arg scope =
  Bind EmptyFC fnName (Pi fc linear Explicit arg) (weaken scope)

export
getFnArgs : Term n vs -> (Term n vs, List (Term n vs))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term n vs) -> Term n vs -> (Term n vs, List (Term n vs))
    getFA args (App _ f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
getFn : Term n vs -> Term n vs
getFn (App _ f a) = getFn f
getFn tm = tm

export %inline
getArgs : Term n vs -> List (Term n vs)
getArgs = snd . getFnArgs

export
isErased : FTerm vs -> Bool
isErased (Erased {}) = True
isErased _ = False

export
getLoc : Term n vs -> FC
getLoc (Local fc _ _) = fc
getLoc (Ref fc _ _) = fc
getLoc (Meta fc _ _) = fc
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
eqTerm : Eq n => Term n vs -> Term n vs' -> Bool
eqTerm (Local _ _ v) (Local _ _ v') = varIdx v == varIdx v'
eqTerm (Ref _ _ n) (Ref _ _ n') = n == n'
eqTerm (Meta _ n args) (Meta _ n' args')
    = n == n' && assert_total (all (uncurry eqTerm) (zip args args'))
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
Eq n => Eq (Term n vs) where (==) = eqTerm

--------------------------------------------------------------------------------
-- Scope checking
--------------------------------------------------------------------------------

rsvL : (vs : Scope) -> List (FTerm vs) -> List (FTerm vs)

rsvB : (vs : Scope) -> Binder (FTerm vs) -> Binder (FTerm vs)

rsvW : (vs : Scope) -> WhyErased (FTerm vs) -> WhyErased (FTerm vs)

rsvP : (vs : Scope) -> PiInfo (FTerm vs) -> PiInfo (FTerm vs)

rsvT : (vs : Scope) -> FTerm vs -> FTerm vs
rsvT vs (Ref fc Bound n)    =
 let Just v  := toVarName n | _ => Ref fc Bound n
     Just nv := isNVar vs v | _ => Ref fc Bound n
  in Local fc (Just False) (forgetName nv)
rsvT vs (Meta fc n ts)      = Meta fc n $ rsvL vs ts
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
resolveNames : (vs : Scope) -> FTerm vs -> FTerm vs
resolveNames = rsvT
