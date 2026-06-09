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

-- TODO: This should probably go to its own module
public export
record Defs (s : Type) where

public export
interface Names (0 s : Type) where
  constructor MkNames
  fullName : Bits32 -> F1 s (Maybe Name)
  nameID   : Name -> F1 s (Maybe Bits32)

public export
interface HasName a where
  full     : Names s => a -> F1 s a
  resolved : Names s => a -> F1 s a


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
  reduceLimit : List (Name, Nat)

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
LocalEnv : Scope -> Scope -> Type

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
      -> Env Term free
      -> Term (Scope.addInner free vars)
      -> Closure free
     MkNFClosure : EvalOpts -> Env Term free -> NF free -> Closure free

data NHead : Scope -> Type where
     NLocal : Maybe Bool -> Var vs -> NHead vs
     NRef   : NameType -> Name -> NHead vs
     NMeta  : Name -> Int -> List (Closure vs) -> NHead vs

data NF : Scope -> Type where
     NBind    :
          FC
      -> (x : Name)
      -> Binder (Closure vs)
      -> ({0 s : _} -> Defs s -> Closure vs -> F1 s (NF vs))
      -> NF vs

     -- Each closure is associated with the file context of the App node that
     -- had it as an argument. It's necessary so as to not lose file context
     -- information when creating the normal form.
     NApp     : FC -> NHead vs -> List (FC, Closure vs) -> NF vs
     NDCon    : FC -> Name -> (tag : Int) -> (arity : Nat) ->
                List (FC, Closure vs) -> NF vs
                -- TODO it looks like the list of closures is stored in spine order, c.f. `getCaseBounds`
     NTCon    : FC -> Name -> (arity : Nat) ->
                List (FC, Closure vs) -> NF vs
     NAs      : FC -> UseSide -> NF vs -> NF vs -> NF vs
     NDelayed : FC -> LazyReason -> NF vs -> NF vs
     NDelay   : FC -> LazyReason -> Closure vs -> Closure vs -> NF vs
     NForce   : FC -> LazyReason -> NF vs -> List (FC, Closure vs) -> NF vs
     NPrimVal : FC -> Constant -> NF vs
     NErased  : FC -> WhyErased (NF vs) -> NF vs
     NType    : FC -> Name -> NF vs

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

export
ntCon : FC -> Name -> Nat -> List (FC, Closure vars) -> NF vars
ntCon fc (UN (Basic "Type")) Z [] = NType fc (MN "top" 0)
ntCon fc n Z [] =
  case isConstantType n of
    Just c  => NPrimVal fc $ PrT c
    Nothing => NTCon fc n Z []
ntCon fc n arity args = NTCon fc n arity args

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
--
-- export
-- HasNames (NHead free) where
--   full defs (NRef nt n) = NRef nt <$> full defs n
--   full defs hd = pure hd
--
--   resolved defs (NRef nt n) = NRef nt <$> resolved defs n
--   resolved defs hd = pure hd
--
-- export
-- HasNames (NF free) where
--   full defs (NBind fc x bd f) = pure $ NBind fc x bd f
--   full defs (NApp fc hd xs) = pure $ NApp fc !(full defs hd) xs
--   full defs (NDCon fc n tag arity xs) = pure $ NDCon fc !(full defs n) tag arity xs
--   full defs (NTCon fc n arity xs) = pure $ NTCon fc !(full defs n) arity xs
--   full defs (NAs fc side nf nf1) = pure $ NAs fc side !(full defs nf) !(full defs nf1)
--   full defs (NDelayed fc lz nf) = pure $ NDelayed fc lz !(full defs nf)
--   full defs (NDelay fc lz cl cl1) = pure $ NDelay fc lz cl cl1
--   full defs (NForce fc lz nf xs) = pure $ NForce fc lz !(full defs nf) xs
--   full defs (NPrimVal fc cst) = pure $ NPrimVal fc cst
--   full defs (NErased fc imp) = pure $ NErased fc imp
--   full defs (NType fc n) = pure $ NType fc !(full defs n)
--
--   resolved defs (NBind fc x bd f) = pure $ NBind fc x bd f
--   resolved defs (NApp fc hd xs) = pure $ NApp fc !(resolved defs hd) xs
--   resolved defs (NDCon fc n tag arity xs) = pure $ NDCon fc !(resolved defs n) tag arity xs
--   resolved defs (NTCon fc n arity xs) = pure $ NTCon fc !(resolved defs n) arity xs
--   resolved defs (NAs fc side nf nf1) = pure $ NAs fc side !(resolved defs nf) !(resolved defs nf1)
--   resolved defs (NDelayed fc lz nf) = pure $ NDelayed fc lz !(resolved defs nf)
--   resolved defs (NDelay fc lz cl cl1) = pure $ NDelay fc lz cl cl1
--   resolved defs (NForce fc lz nf xs) = pure $ NForce fc lz !(resolved defs nf) xs
--   resolved defs (NPrimVal fc cst) = pure $ NPrimVal fc cst
--   resolved defs (NErased fc imp) = pure $ NErased fc imp
--   resolved defs (NType fc n) = pure $ NType fc !(resolved defs n)
