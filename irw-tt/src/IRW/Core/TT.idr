module IRW.Core.TT

import Data.Maybe
import Data.SortedMap
import Decidable.HDecEq
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

%default total
%language ElabReflection
%hide Language.Reflection.TT.FC
%hide Language.Reflection.TT.NameType
%hide Language.Reflection.TT.PiInfo
%hide Language.Reflection.TT.TotalReq
%hide Language.Reflection.TT.Visibility
%hide Language.Reflection.TTImp.DataOpt

public export
record KindedName where
  constructor MkKindedName
  nameKind : Maybe NameType
  fullName : FullName -- fully qualified name

%runElab derive "KindedName" [Show,Eq]

export %inline
Interpolation KindedName where interpolate = interpolate . ref . fullName

%name KindedName kn

export
defaultKindedName : FullName -> KindedName
defaultKindedName nm = MkKindedName Nothing nm

export
funKindedName : FullName -> KindedName
funKindedName nm = MkKindedName (Just Func) nm

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
    Add  : (x : VarName) -> VarName -> Bounds sx -> Bounds (sx:<x)

  export
  sizeOf : Bounds sx -> SizeOf sx
  sizeOf None        = zero
  sizeOf (Add _ _ b) = suc (sizeOf b)

export %inline
addVars :
     {auto gw : GenWeaken tm}
  -> SizeOf outer
  -> Bounds bound
  -> tm (vs++outer)
  -> tm ((vs++bound)++outer)
addVars p = genWeakenNs p . sizeOf

export
resolveRef :
     SizeOf outer
  -> LSizeOf done
  -> Bounds bound
  -> FC
  -> VarName
  -> Maybe (Var (((vs ++ bound) <>< done) ++ outer))
resolveRef _ _ None _ _ = Nothing
resolveRef {outer} {vs} {done} p q (Add {sx} new old bs) fc n =
  if n == old
    then Just (weakenNs p $ mkVarFishly q)
    else resolveRef p (suc q) bs fc n

locB : SizeOf o -> Bounds b -> Binder (FTerm $ vs++o) -> Binder (FTerm $ (vs++b)++o)

locP : SizeOf o -> Bounds b -> PiInfo (FTerm $ vs++o) -> PiInfo (FTerm $ (vs++b)++o)

locW : SizeOf o -> Bounds b -> WhyErased (FTerm $ vs++o) -> WhyErased (FTerm $ (vs++b)++o)

locL : SizeOf o -> Bounds b -> List (FTerm $ vs++o) -> List (FTerm $ (vs++b)++o)

locT : SizeOf o -> Bounds b -> FTerm (vs++o) -> FTerm ((vs++b)++o)
locT o bs (Local fc r v) = Local fc r (addVars o bs v)
locT o bs (Ref fc Bound n) =
 let Just vn := toVarName n | _ => Ref fc Bound n
     Just v  := resolveRef o zero bs fc vn | _ => Ref fc Bound n
  in Local fc Nothing v
locT o bs (Ref fc nt n) = Ref fc nt n
locT o bs (Meta fc n xs) = Meta fc n (locL o bs xs)
locT o bs (Bind fc x b sc) = Bind fc x (locB o bs b) (locT (suc o) bs sc)
locT o bs (App fc fn arg) = App fc (locT o bs fn) (locT o bs arg)
locT o bs (As fc s as tm) = As fc s (locT o bs as) (locT o bs tm)
locT o bs (TDelayed fc x y) = TDelayed fc x (locT o bs y)
locT o bs (TDelay fc x t y) = TDelay fc x (locT o bs t) (locT o bs y)
locT o bs (TForce fc r x) = TForce fc r (locT o bs x)
locT o bs (PrimVal fc c) = PrimVal fc c
locT o bs (Erased fc w) = Erased fc (locW o bs w)
locT o bs (TType fc u) = TType fc u

locL o bs []      = []
locL o bs (t::ts) = locT o bs t :: locL o bs ts

locW o bs Placeholder = Placeholder
locW o bs Impossible  = Impossible
locW o bs (Dotted x)  = Dotted $ locT o bs x

locP o bs Implicit        = Implicit
locP o bs Explicit        = Explicit
locP o bs AutoImplicit    = AutoImplicit
locP o bs (DefImplicit x) = DefImplicit $ locT o bs x

locB o bs (Lam fc r p t)  = Lam fc r  (locP o bs p) (locT o bs t)
locB o bs (Let fc r v t)  = Let fc r  (locT o bs v) (locT o bs t)
locB o bs (Pi fc r p t)   = Pi fc r   (locP o bs p) (locT o bs t)
locB o bs (PVar fc r p t) = PVar fc r (locP o bs p) (locT o bs t)
locB o bs (PLet fc r v t) = PLet fc r (locT o bs v) (locT o bs t)
locB o bs (PVTy fc r t)   = PVTy fc r (locT o bs t)

export
refsToLocals : Bounds b -> FTerm vs -> FTerm (vs++b)
refsToLocals None y = y
refsToLocals bs   y = locT zero  bs y

||| Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : VarName) -> (new : VarName) -> FTerm vs -> FTerm (vs:<new)
refToLocal x new tm = refsToLocals (Add new x None) tm

subB : Eq n => n -> Term n vs -> Binder (Term n vs) -> Binder (Term n vs)

subP : Eq n => n -> Term n vs -> PiInfo (Term n vs) -> PiInfo (Term n vs)

subL : Eq n => n -> Term n vs -> List (Term n vs) -> List (Term n vs)

subT : Eq n => n -> Term n vs -> Term n vs -> Term n vs
subT n x (Ref fc nt m) = if n == m then x else Ref fc nt m
subT n x (Meta fc m xs) = Meta fc m (subL n x xs)
subT n x (Bind fc y b sc) = Bind fc y (subB n x b) (subT n (weaken x) sc)
subT n x (App fc fn arg) = App fc (subT n x fn) (subT n x arg)
subT n x (As fc s as pat) = As fc s as (subT n x pat)
subT n x (TDelayed fc y z) = TDelayed fc y (subT n x z)
subT n x (TDelay fc y t z) = TDelay fc y (subT n x t) (subT n x z)
subT n x (TForce fc r y) = TForce fc r (subT n x y)
subT n x tm = tm

subL n x []      = []
subL n x (t::ts) = subT n x t :: subL n x ts

subP n x Implicit        = Implicit
subP n x Explicit        = Explicit
subP n x AutoImplicit    = AutoImplicit
subP n x (DefImplicit y) = DefImplicit $ subT n x y

subB n x (Lam fc r p t)  = Lam fc r  (subP n x p) (subT n x t)
subB n x (Let fc r v t)  = Let fc r  (subT n x v) (subT n x t)
subB n x (Pi fc r p t)   = Pi fc r   (subP n x p) (subT n x t)
subB n x (PVar fc r p t) = PVar fc r (subP n x p) (subT n x t)
subB n x (PLet fc r v t) = PLet fc r (subT n x v) (subT n x t)
subB n x (PVTy fc r t)   = PVTy fc r (subT n x t)

||| Replace an explicit name with a term
export %inline
substName : Eq n => n -> Term n vs -> Term n vs -> Term n vs
substName = subT
