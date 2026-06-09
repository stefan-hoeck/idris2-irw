module IRW.Core.Value

import Data.SnocList.Quantifiers
import Derive.Prelude
import IRW.Core.Env
import IRW.Core.Name
import IRW.Core.Name.Scoped
import IRW.Core.TT
import Data.Linear.Token

%default total
%language ElabReflection
%hide Language.Reflection.TT.FC
%hide Language.Reflection.TT.LazyReason
%hide Language.Reflection.TT.Constant
%hide Language.Reflection.TTImp.UseSide
%hide Language.Reflection.TT.Name
%hide Language.Reflection.TT.NameType

public export
record Defs (s : Type) where

public export
data EvalOrder = CBV | CBN

%runElab derive "EvalOrder" [Show,Eq,Ord]

public export
record EvalOpts where
  constructor MkEvalOpts
  ||| only evaluate hole solutions
  holesOnly : Bool

  ||| only evaluate holes which are relevant arguments
  argHolesOnly : Bool

  ||| reduce 'as' patterns (don't do this on LHS)
  removeAs : Bool

  ||| evaluate everything, including private names
  evalAll : Bool

  ||| inline for totality checking
  tcInline : Bool

  ||| Limit for recursion depth
  fuel : Maybe Nat

  ||| reduction limits for given names. If not present, no limit
  reduceLimit : List (FullName, Nat)

  ||| evaluation order
  strategy : EvalOrder

%runElab derive "EvalOpts" [Show,Eq]

export
defaultOpts : EvalOpts
defaultOpts =
  MkEvalOpts
    { holesOnly = False
    , argHolesOnly = False
    , removeAs = True
    , evalAll = False
    , tcInline = False
    , fuel = Nothing
    , reduceLimit = []
    , strategy = CBN
    }

export
withHoles : EvalOpts
withHoles =
  MkEvalOpts
    { holesOnly = True
    , argHolesOnly = True
    , removeAs = False
    , evalAll = False
    , tcInline = False
    , fuel = Nothing
    , reduceLimit = []
    , strategy = CBN
    }

export
withAll : EvalOpts
withAll =
  MkEvalOpts
    { holesOnly = False
    , argHolesOnly = False
    , removeAs = True
    , evalAll = True
    , tcInline = False
    , fuel = Nothing
    , reduceLimit = []
    , strategy = CBN
    }

export
withArgHoles : EvalOpts
withArgHoles =
  MkEvalOpts
    { holesOnly = False
    , argHolesOnly = True
    , removeAs = False
    , evalAll = False
    , tcInline = False
    , fuel = Nothing
    , reduceLimit = []
    , strategy = CBN
    }

export
tcOnly : EvalOpts
tcOnly = { tcInline := True } withArgHoles

export
onLHS : EvalOpts
onLHS = { removeAs := False } defaultOpts

export
cbn : EvalOpts
cbn = defaultOpts

export
cbv : EvalOpts
cbv = { strategy := CBV } defaultOpts

public export
0 LocalEnv : Scope -> Scope -> Type

||| The head of a value: things you can apply arguments to
public export
data NHead : Scope -> Type

||| Values themselves. 'Closure' is an unevaluated thunk, which means
||| we can wait until necessary to reduce constructor arguments
public export
data NF : Scope -> Type

public export
data Closure : Scope -> Type where
     MkClosure :
         {vars : _}
      -> (opts : EvalOpts)
      -> LocalEnv free vars
      -> Env FTerm free
      -> FTerm (Scope.addInner free vars)
      -> Closure free
     MkNFClosure : EvalOpts -> Env FTerm free -> NF free -> Closure free

data NHead : Scope -> Type where
     NLocal : Maybe Bool -> Var vs -> NHead vs
     NRef   : NameType -> FullName -> NHead vs
     NMeta  : VarName -> List (Closure vs) -> NHead vs

data NF : Scope -> Type where
     NBind    :
          FC
      -> (x : VarName)
      -> Binder (Closure vs)
      -> ({0 s : _} -> Defs s -> Closure vs -> F1 s (NF vs))
      -> NF vs

     -- Each closure is associated with the file context of the App node that
     -- had it as an argument. It's necessary so as to not lose file context
     -- information when creating the normal form.
     NApp     : FC -> NHead vs -> List (FC, Closure vs) -> NF vs
     NDCon    : FC -> FullName -> (tag : Bits32) -> (arity : Nat) ->
                List (FC, Closure vs) -> NF vs
                -- TODO it looks like the list of closures is stored in spine order, c.f. `getCaseBounds`
     NTCon    : FC -> FullName -> (arity : Nat) ->
                List (FC, Closure vs) -> NF vs
     NAs      : FC -> UseSide -> NF vs -> NF vs -> NF vs
     NDelayed : FC -> LazyReason -> NF vs -> NF vs
     NDelay   : FC -> LazyReason -> Closure vs -> Closure vs -> NF vs
     NForce   : FC -> LazyReason -> NF vs -> List (FC, Closure vs) -> NF vs
     NPrimVal : FC -> Constant -> NF vs
     NErased  : FC -> WhyErased (NF vs) -> NF vs
     NType    : FC -> VarName -> NF vs

LocalEnv free = All (\_ => Closure free)

%name LocalEnv lenv
%name Closure cl
%name NHead hd
%name NF nf

public export
0 ClosedClosure : Type
ClosedClosure = Closure [<]

public export
0 ClosedNF : Type
ClosedNF = NF [<]

namespace LocalEnv
  public export
  empty : LocalEnv free Scope.empty
  empty = [<]

-- export
-- ntCon : FC -> FullName -> Nat -> List (FC, Closure vars) -> NF vars
-- ntCon fc (UN (Basic "Type")) Z [] = NType fc (MN "top" 0)
-- ntCon fc n Z [] =
--   case isConstantType n of
--     Just c  => NPrimVal fc $ PrT c
--     Nothing => NTCon fc n Z []
-- ntCon fc n arity args = NTCon fc n arity args

export
getLoc : NF vs -> FC
getLoc (NBind fc _ _ _) = fc
getLoc (NApp fc _ _) = fc
getLoc (NDCon fc _ _ _ _) = fc
getLoc (NTCon fc _ _ _) = fc
getLoc (NAs fc _ _ _) = fc
getLoc (NDelayed fc _ _) = fc
getLoc (NDelay fc _ _ _) = fc
getLoc (NForce fc _ _ _) = fc
getLoc (NPrimVal fc _) = fc
getLoc (NErased fc i) = fc
getLoc (NType fc _) = fc
