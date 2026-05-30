module IRW.Core.Name.Namespace

import Data.List
import Decidable.Equality
import Derive.Prelude
import IRW.Libs.Data.String.Extra

%default total
%language ElabReflection
%hide Language.Reflection.TT.ModuleIdent
%hide Language.Reflection.TT.Namespace
%hide Language.Reflection.TT.MkNS

-------------------------------------------------------------------------------------
-- TYPES
-------------------------------------------------------------------------------------

||| Nested namespaces are stored in reverse order.
||| i.e. `X.Y.Z.foo` will be represented as `NS [Z,Y,X] foo`
||| As a consequence we hide the representation behind an opaque type alias
||| and force users to manufacture and manipulate namespaces via the safe
||| functions we provide.
public export
record Namespace where
  constructor MkNS
  names : SnocList String

%runElab derive "Namespace" [Show,Eq,Ord,Semigroup,Monoid]

%name Namespace ns

||| A Module Identifier is, similarly to a namespace, stored inside out.
public export
record ModuleIdent where
  constructor MkMI
  modules : SnocList String

%runElab derive "ModuleIdent" [Show,Eq,Ord,Semigroup,Monoid]

%name ModuleIdent mi

export %inline
Cast Namespace ModuleIdent where cast (MkNS x) = MkMI x

export %inline
Cast ModuleIdent Namespace where cast (MkMI x) = MkNS x

-------------------------------------------------------------------------------------
-- SMART CONSTRUCTORS
-------------------------------------------------------------------------------------

export
mkNamespacedIdent : String -> (Maybe Namespace, String)
mkNamespacedIdent s =
  case [<] <>< forget (split (== '.') s) of
    [<n]  => (Nothing, n)
    ns:<n => (Just $ MkNS ns, n)
    [<]   => (Nothing, "") 

export
mkNestedNamespace : Maybe Namespace -> String -> Namespace
mkNestedNamespace Nothing n = MkNS [<n]
mkNestedNamespace (Just (MkNS ns)) n = MkNS $ ns :< n

export
mkNamespace : String -> Namespace
mkNamespace "" = MkNS [<]
mkNamespace s  = uncurry mkNestedNamespace (mkNamespacedIdent s)

export
mkModuleIdent : Maybe Namespace -> String -> ModuleIdent
mkModuleIdent Nothing n = MkMI [<n]
mkModuleIdent (Just (MkNS ns)) n = MkMI $ ns :< n

-------------------------------------------------------------------------------------
-- MANIPULATING NAMESPACES
-------------------------------------------------------------------------------------

export
replace : (old : ModuleIdent) -> (new, ns : Namespace) -> Namespace
replace (MkMI old) (MkNS new) (MkNS ns) = MkNS (go ns)
  where
    go : SnocList String -> SnocList String
    go [<]       = [<]
    go x@(ms:<m) = if old == x then new else go ms :< m

namespace ModuleIdent
  ||| A.B.C -> "A/B/C"
  export %inline
  toPath : ModuleIdent -> String
  toPath = snocSep "/" . modules

  export %inline
  parent : ModuleIdent -> Maybe ModuleIdent
  parent (MkMI $ r :< _) = Just $ MkMI r
  parent _               = Nothing

-------------------------------------------------------------------------------------
-- HIERARCHICAL STRUCTURE
-------------------------------------------------------------------------------------

||| Nested namespaces naturally give rise to a hierarchical structure. In particular
||| from a given namespace we can compute all of the parent (aka englobing) ones.
||| For instance `allParents Data.List.Properties` should yield a set containing
||| both `Data.List` and `Data` (no guarantee is given on the order).
export
allParents : Namespace -> List Namespace
allParents = go . names
  where
    go : SnocList String -> List Namespace
    go [<]       = []
    go x@(ns:<n) = MkNS x :: go ns

||| We can check whether a given namespace is a parent (aka englobing) namespace
||| of a candidate namespace.
||| We expect that `all (\ p => isParentOf p ns) (allParents ns)` holds true.
export
isParentOf : (given, candidate : Namespace) -> Bool
isParentOf (MkNS ms) (MkNS ns) = isPrefixOf (ms<>>[]) (ns<>>[])

||| When writing qualified names users often do not want to spell out the full
||| namespace, rightly considering that an unambiguous segment should be enough.
||| This function checks whether a candidate is an approximation of a given
||| namespace.
||| We expect `isApproximationOf List.Properties Data.List.Properties` to hold true
||| while `isApproximationOf Data.List Data.List.Properties` should not.
export
isApproximationOf : (given, candidate : Namespace) -> Bool
isApproximationOf (MkNS ms) (MkNS ns) = isPrefixOf (ms <>> []) (ns <>> [])

||| We can check whether a given string (assumed to be a valid Namespace ident)
||| is in the path of a given namespace.
export
isInPathOf : (i : String) -> (candidate : Namespace) -> Bool
isInPathOf i (MkNS ns) = i `elem` ns

-------------------------------------------------------------------------------------
-- INSTANCES
-------------------------------------------------------------------------------------

Injective MkNS where
  injective Refl = Refl

export
DecEq Namespace where
  decEq (MkNS ms) (MkNS ns) = decEqCong (decEq ms ns)

export %inline
showNSWithSep : String -> Namespace -> String
showNSWithSep sep = snocSep sep . names

export %inline
Interpolation Namespace where interpolate = showNSWithSep "."

export %inline
Interpolation ModuleIdent where interpolate = interpolate . cast {to = Namespace}

-------------------------------------------------------------------------------------
-- CONSTANTS
-------------------------------------------------------------------------------------

||| This is used when evaluating things in the REPL
export
emptyNS : Namespace
emptyNS = neutral

export
mainNS : Namespace
mainNS = mkNamespace "Main"

export
partialEvalNS : Namespace
partialEvalNS = mkNamespace "_PE"

export
builtinNS : Namespace
builtinNS = mkNamespace "Builtin"

export
preludeNS : Namespace
preludeNS = mkNamespace "Prelude"

export
numNS : Namespace
numNS = mkNamespace "Prelude.Num"

export
typesNS : Namespace
typesNS = mkNamespace "Prelude.Types"

export
basicsNS : Namespace
basicsNS = mkNamespace "Prelude.Basics"

export
eqOrdNS : Namespace
eqOrdNS = mkNamespace "Prelude.EqOrd"

export
primIONS : Namespace
primIONS = mkNamespace "PrimIO"

export
ioNS : Namespace
ioNS = mkNamespace "Prelude.IO"

export
reflectionNS : Namespace
reflectionNS = mkNamespace "Language.Reflection"

export
reflectionTTNS : Namespace
reflectionTTNS = mkNamespace "Language.Reflection.TT"

export
reflectionTTImpNS : Namespace
reflectionTTImpNS = mkNamespace "Language.Reflection.TTImp"

export
dpairNS : Namespace
dpairNS = mkNamespace "Builtin.DPair"

export
natNS : Namespace
natNS = mkNamespace "Data.Nat"
