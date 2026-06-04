module IRW.Core.TT

import Data.Maybe
import Derive.Prelude
import IRW.Libs.Data.SizeOf

import public IRW.Algebra
import public IRW.Core.FC
import public IRW.Core.Name
import public IRW.Core.Name.Scoped
import public IRW.Core.TT.Binder
import public IRW.Core.TT.Primitive
import public IRW.Core.TT.Subst
import public IRW.Core.TT.Term
import public IRW.Core.TT.Term.Subst
import public IRW.Core.TT.Var

%default covering
%language ElabReflection
%hide Language.Reflection.TT.FC
%hide Language.Reflection.TT.Name
%hide Language.Reflection.TT.NameType
%hide Language.Reflection.TT.TotalReq
%hide Language.Reflection.TT.Visibility
%hide Language.Reflection.TTImp.DataOpt

public export
record KindedName where
  constructor MkKindedName
  nameKind : Maybe NameType
  fullName : Name -- fully qualified name
  rawName  : Name

%runElab derive "KindedName" [Show,Eq]

export %inline
Interpolation KindedName where interpolate = interpolate . rawName

%name KindedName kn

export
defaultKindedName : Name -> KindedName
defaultKindedName nm = MkKindedName Nothing nm nm

export
funKindedName : Name -> KindedName
funKindedName nm = MkKindedName (Just Func) nm nm

public export
data Visibility = Private | Export | Public

%runElab derive "Visibility" [Show,Eq,Ord]

%name Visibility vis

export
Interpolation Visibility where
  interpolate Private = "private"
  interpolate Export = "export"
  interpolate Public = "public export"

public export
data DataOpt : Type where
  ||| Determining arguments during proof search
  SearchBy : List1 Name -> DataOpt
  ||| Don't generate constructor search hints
  NoHints : DataOpt
  ||| Auto-implicit search must check result is unique
  UniqueSearch : DataOpt
  ||| Implemented externally
  External : DataOpt
  ||| Don't apply newtype optimisation
  NoNewtype : DataOpt

%runElab derive "DataOpt" [Show,Eq]

%name DataOpt dopt

public export
data Fixity = InfixL | InfixR | Infix | Prefix

%runElab derive "Fixity" [Show,Eq]

export %inline
Interpolation Fixity where
  interpolate = toLower . show

public export
data BindingModifier = NotBinding | Autobind | Typebind

%runElab derive "BindingModifier" [Show,Eq]

export
Interpolation BindingModifier where
  interpolate NotBinding = "regular"
  interpolate Typebind   = "typebind"
  interpolate Autobind   = "autobind"

-- A record to hold all the information about a fixity
public export
record FixityInfo where
  constructor MkFixityInfo
  fc : FC
  vis : Visibility
  bindingInfo : BindingModifier
  fix : Fixity
  precedence : Nat

%runElab derive "FixityInfo" [Show,Eq]

||| Whenever we read an operator from the parser,
||| we don't know if it's a backticked expression with no fixity
||| declaration, or if it has a fixity declaration.
||| If it does not have a declaration, we represent this state
||| with `UndeclaredFixity`.
||| Note that a backticked expression can have a
||| fixity declaration, in which case it is represented with
||| `DeclaredFixity`.
public export
data FixityDeclarationInfo = UndeclaredFixity | DeclaredFixity FixityInfo

%runElab derive "FixityDeclarationInfo" [Show,Eq]

||| Left-hand-side information for operators, carries autobind information
||| an operator can either be
||| - not autobind, a regular operator
||| - binding types, such that `(nm : ty) =@ fn nm
||| ` desugars into `(=@) ty (\(nm : ty) => fn nm)`
||| - binding expressing with an inferred type such that
|||   `(nm := exp) =@ fn nm` desugars into `(=@) exp (\(nm : ?) => fn nm)`
||| - binding both types and expression such that
|||   `(nm : ty := exp) =@ fn nm` desugars into `(=@) exp (\(nm : ty) => fn nm)`
public export
data OperatorLHSInfo : Type -> Type where
  ||| Traditional operator wihtout binding, carries the lhs
  NoBinder : (lhs : t) -> OperatorLHSInfo t
  ||| (nm : ty) =@ fn x
  BindType : (name : t) -> (ty : t) -> OperatorLHSInfo t
  ||| (nm := exp) =@ fn nm
  BindExpr : (name : t) -> (expr : t) -> OperatorLHSInfo t
  ||| (nm : ty := exp) =@ fn nm
  BindExplicitType : (name : t) -> (type, expr : t) -> OperatorLHSInfo t

%runElab derive "OperatorLHSInfo" [Show]

export
Interpolation (OperatorLHSInfo tm) where
  interpolate (NoBinder {})         = "regular"
  interpolate (BindType {})         = "type-binding (typebind)"
  interpolate (BindExpr {})         = "automatically-binding (autobind)"
  interpolate (BindExplicitType {}) = "automatically-binding (autobind)"

%name OperatorLHSInfo opInfo

export
Functor OperatorLHSInfo where
  map f (NoBinder lhs) = NoBinder $ f lhs
  map f (BindType nm lhs) = BindType (f nm) (f lhs)
  map f (BindExpr nm lhs) = BindExpr (f nm) (f lhs)
  map f (BindExplicitType nm ty lhs) = BindExplicitType (f nm) (f ty) (f lhs)

export
(.getLhs) : OperatorLHSInfo tm -> tm
(.getLhs) (NoBinder lhs) = lhs
(.getLhs) (BindExpr _ lhs) = lhs
(.getLhs) (BindType _ lhs) = lhs
(.getLhs) (BindExplicitType _ _ lhs) = lhs

export
(.getBoundPat) : OperatorLHSInfo tm -> Maybe tm
(.getBoundPat) (NoBinder lhs) = Nothing
(.getBoundPat) (BindType name ty) = Just name
(.getBoundPat) (BindExpr name expr) = Just name
(.getBoundPat) (BindExplicitType name type expr) = Just name

export
(.getBinder) : OperatorLHSInfo tm -> BindingModifier
(.getBinder) (NoBinder lhs) = NotBinding
(.getBinder) (BindType name ty) = Typebind
(.getBinder) (BindExpr name expr) = Autobind
(.getBinder) (BindExplicitType name type expr) = Autobind

public export
data TotalReq = PartialOK | CoveringOnly | Total

%runElab derive "TotalReq" [Show,Eq,Ord]

%name TotalReq treq

export
Interpolation TotalReq where
  interpolate Total        = "total"
  interpolate CoveringOnly = "covering"
  interpolate PartialOK    = "partial"

public export
data PartialReason
       = NotStrictlyPositive
       | BadCall (List Name)
       -- sequence of mutually-recursive function calls leading to a non-terminating function
       | BadPath (List (FC, Name)) Name
       | RecPath (List (FC, Name))

%runElab derive "PartialReason" [Show,Eq]

export
Interpolation PartialReason where
  interpolate NotStrictlyPositive = "not strictly positive"
  interpolate (BadCall [n]) = "possibly not terminating due to call to \{n}"
  interpolate (BadCall ns) =
   let s := joinBy ", " (map interpolate ns)
    in "possibly not terminating due to calls to \{s}"
  interpolate (BadPath [_] n) = "possibly not terminating due to call to \{n}"
  interpolate (BadPath init n) =
   let s := joinBy " -> " (map (interpolate . snd) init)
    in "possibly not terminating due to function \{n} being reachable via \{s}"
  interpolate (RecPath loop) =
   let s := joinBy " -> " (map (interpolate . snd) loop)
    in "possibly not terminating due to recursive path \{s}"

public export
data Terminating
       = Unchecked
       | IsTerminating
       | NotTerminating PartialReason

%runElab derive "Terminating" [Show,Eq]

export
Interpolation Terminating where
  interpolate Unchecked = "not yet checked"
  interpolate IsTerminating = "terminating"
  interpolate (NotTerminating p) = interpolate p

public export
data Covering
       = IsCovering
       | MissingCases (List ClosedTerm)
       | NonCoveringCall (List Name)

%runElab derive "Covering" [Show,Eq]

export
Interpolation Covering where
  interpolate IsCovering = "covering"
  interpolate (MissingCases c) = "not covering all cases"
  interpolate (NonCoveringCall [f]) = "not covering due to call to function \{f}"
  interpolate (NonCoveringCall cs) =
   let s := joinBy ", " (map interpolate cs)
    in "not covering due to calls to functions \{s}"

||| Totality status of a definition. We separate termination checking from
||| coverage checking.
public export
record Totality where
  constructor MkTotality
  isTerminating : Terminating
  isCovering : Covering

%runElab derive "Totality" [Show,Eq]

export
Interpolation Totality where
  interpolate tot =
    let t := isTerminating tot
        c := isCovering tot
     in showTot t c
    where
      showTot : Terminating -> Covering -> String
      showTot IsTerminating IsCovering = "total"
      showTot IsTerminating c = interpolate c
      showTot t IsCovering = interpolate t
      showTot t c = "\{c}; \{t}"

export
unchecked : Totality
unchecked = MkTotality Unchecked IsCovering

export
isTotal : Totality
isTotal = MkTotality Unchecked IsCovering

export
notCovering : Totality
notCovering = MkTotality Unchecked (MissingCases [])

namespace Bounds
  public export
  data Bounds : Scoped where
    None : Bounds Scope.empty
    Add  : (x : Name) -> Name -> Bounds sx -> Bounds (sx:<x)

  export
  sizeOf : Bounds sx -> SizeOf sx
  sizeOf None        = zero
  sizeOf (Add _ _ b) = suc (sizeOf b)

export
addVars :
     SizeOf outer
  -> Bounds bound
  -> NVar n (vs++outer)
  -> NVar n ((vs++bound)++outer)
addVars p = insertNVarNames p . sizeOf

export
resolveRef :
     SizeOf outer
  -> LSizeOf done
  -> Bounds bound
  -> FC
  -> Name
  -> Maybe (Var (((vs ++ bound) <>< done) ++ outer))
resolveRef _ _ None _ _ = Nothing
resolveRef {outer} {vs} {done} p q (Add {sx} new old bs) fc n =
  if n == old
    then Just (weakenNs p $ mkVarFishly q)
    else resolveRef p (suc q) bs fc n

-- mkLocals : SizeOf outer -> Bounds bound ->
--            Term (outer ++ vars) -> Term (outer ++ (bound ++ vars))
-- mkLocals outer bs (Local fc r idx p)
--     = let MkNVar p' = addVars outer bs (MkNVar p) in Local fc r _ p'
-- mkLocals outer bs (Ref fc Bound name)
--     = fromMaybe (Ref fc Bound name) $ do
--         MkVar p <- resolveRef outer [<] bs fc name
--         pure (Local fc Nothing _ p)
-- mkLocals outer bs (Ref fc nt name)
--     = Ref fc nt name
-- mkLocals outer bs (Meta fc name y xs)
--     = fromMaybe (Meta fc name y (map (mkLocals outer bs) xs)) $ do
--         MkVar p <- resolveRef outer [<] bs fc name
--         pure (Local fc Nothing _ p)
-- mkLocals outer bs (Bind fc x b scope)
--     = Bind fc x (map (mkLocals outer bs) b)
--            (mkLocals (suc outer) bs scope)
-- mkLocals outer bs (App fc fn arg)
--     = App fc (mkLocals outer bs fn) (mkLocals outer bs arg)
-- mkLocals outer bs (As fc s as tm)
--     = As fc s (mkLocals outer bs as) (mkLocals outer bs tm)
-- mkLocals outer bs (TDelayed fc x y)
--     = TDelayed fc x (mkLocals outer bs y)
-- mkLocals outer bs (TDelay fc x t y)
--     = TDelay fc x (mkLocals outer bs t) (mkLocals outer bs y)
-- mkLocals outer bs (TForce fc r x)
--     = TForce fc r (mkLocals outer bs x)
-- mkLocals outer bs (PrimVal fc c) = PrimVal fc c
-- mkLocals outer bs (Erased fc Impossible) = Erased fc Impossible
-- mkLocals outer bs (Erased fc Placeholder) = Erased fc Placeholder
-- mkLocals outer bs (Erased fc (Dotted t)) = Erased fc (Dotted (mkLocals outer bs t))
-- mkLocals outer bs (TType fc u) = TType fc u
--
-- export
-- refsToLocals : Bounds bound -> Term vars -> Term (bound ++ vars)
-- refsToLocals None y = y
-- refsToLocals bs y = mkLocals zero  bs y
--
-- -- Replace any reference to 'x' with a locally bound name 'new'
-- export
-- refToLocal : (x : Name) -> (new : Name) -> Term vars -> Term (new :: vars)
-- refToLocal x new tm = refsToLocals (Add new x None) tm
--
-- -- Replace an explicit name with a term
-- export
-- substName : Name -> Term vars -> Term vars -> Term vars
-- substName x new (Ref fc nt name)
--     = case nameEq x name of
--            Nothing => Ref fc nt name
--            Just Refl => new
-- substName x new (Meta fc n i xs)
--     = Meta fc n i (map (substName x new) xs)
-- -- ASSUMPTION: When we substitute under binders, the name has always been
-- -- resolved to a Local, so no need to check that x isn't shadowing
-- substName x new (Bind fc y b scope)
--     = Bind fc y (map (substName x new) b) (substName x (weaken new) scope)
-- substName x new (App fc fn arg)
--     = App fc (substName x new fn) (substName x new arg)
-- substName x new (As fc s as pat)
--     = As fc s as (substName x new pat)
-- substName x new (TDelayed fc y z)
--     = TDelayed fc y (substName x new z)
-- substName x new (TDelay fc y t z)
--     = TDelay fc y (substName x new t) (substName x new z)
-- substName x new (TForce fc r y)
--     = TForce fc r (substName x new y)
-- substName x new tm = tm
--
-- export
-- addMetas : (usingResolved : Bool) -> NameMap Bool -> Term vars -> NameMap Bool
-- addMetas res ns (Local fc x idx y) = ns
-- addMetas res ns (Ref fc x name) = ns
-- addMetas res ns (Meta fc n i xs)
--   = addMetaArgs (insert (ifThenElse res (Resolved i) n) False ns) xs
--   where
--     addMetaArgs : NameMap Bool -> List (Term vars) -> NameMap Bool
--     addMetaArgs ns [] = ns
--     addMetaArgs ns (t :: ts) = addMetaArgs (addMetas res ns t) ts
-- addMetas res ns (Bind fc x (Let _ c val ty) scope)
--     = addMetas res (addMetas res (addMetas res ns val) ty) scope
-- addMetas res ns (Bind fc x b scope)
--     = addMetas res (addMetas res ns (binderType b)) scope
-- addMetas res ns (App fc fn arg)
--     = addMetas res (addMetas res ns fn) arg
-- addMetas res ns (As fc s as tm) = addMetas res ns tm
-- addMetas res ns (TDelayed fc x y) = addMetas res ns y
-- addMetas res ns (TDelay fc x t y)
--     = addMetas res (addMetas res ns t) y
-- addMetas res ns (TForce fc r x) = addMetas res ns x
-- addMetas res ns (PrimVal fc c) = ns
-- addMetas res ns (Erased fc i) = foldr (flip $ addMetas res) ns i
-- addMetas res ns (TType fc u) = ns
--
-- -- Get the metavariable names in a term
-- export
-- getMetas : Term vars -> NameMap Bool
-- getMetas tm = addMetas False empty tm
--
-- export
-- addRefs : (underAssert : Bool) -> (aTotal : Name) ->
--           NameMap Bool -> Term vars -> NameMap Bool
-- addRefs ua at ns (Local fc x idx y) = ns
-- addRefs ua at ns (Ref fc x name) = insert name ua ns
-- addRefs ua at ns (Meta fc n i xs)
--     = addRefsArgs ns xs
--   where
--     addRefsArgs : NameMap Bool -> List (Term vars) -> NameMap Bool
--     addRefsArgs ns [] = ns
--     addRefsArgs ns (t :: ts) = addRefsArgs (addRefs ua at ns t) ts
-- addRefs ua at ns (Bind fc x (Let _ c val ty) scope)
--     = addRefs ua at (addRefs ua at (addRefs ua at ns val) ty) scope
-- addRefs ua at ns (Bind fc x b scope)
--     = addRefs ua at (addRefs ua at ns (binderType b)) scope
-- addRefs ua at ns (App _ (App _ (Ref fc _ name) x) y)
--     = if name == at
--          then addRefs True at (insert name True ns) y
--          else addRefs ua at (addRefs ua at (insert name ua ns) x) y
-- addRefs ua at ns (App fc fn arg)
--     = addRefs ua at (addRefs ua at ns fn) arg
-- addRefs ua at ns (As fc s as tm) = addRefs ua at ns tm
-- addRefs ua at ns (TDelayed fc x y) = addRefs ua at ns y
-- addRefs ua at ns (TDelay fc x t y)
--     = addRefs ua at (addRefs ua at ns t) y
-- addRefs ua at ns (TForce fc r x) = addRefs ua at ns x
-- addRefs ua at ns (PrimVal fc c) = ns
-- addRefs ua at ns (Erased fc i) = foldr (flip $ addRefs ua at) ns i
-- addRefs ua at ns (TType fc u) = ns
--
-- -- As above, but for references. Also flag whether a name is under an
-- -- 'assert_total' because we may need to know that in coverage/totality
-- -- checking
-- export
-- getRefs : (aTotal : Name) -> Term vars -> NameMap Bool
-- getRefs at tm = addRefs False at empty tm
