module IRW.Core.Name

import Data.Maybe0 as M0
import Data.SnocList
import Decidable.HDecEq
import Derive.Prelude
import IRW.Libs.Data.String.Extra
import IRW.Libs.Text.Distance.Levenshtein as D

import public IRW.Core.Name.Namespace

%default total
%language ElabReflection

%hide Derive.Eq.conIndexName
%hide Language.Reflection.TT.ModuleIdent
%hide Language.Reflection.TT.Name
%hide Language.Reflection.TT.Namespace
%hide Language.Reflection.TT.UserName

||| A username has some structure
public export
data UserName : Type where
  Basic : String -> UserName -- default name constructor       e.g. map
  Field : String -> UserName -- field accessor                 e.g. .fst
  Underscore : UserName      -- no name                        e.g. _

%runElab derive "UserName" [Show,Eq,Ord]
%name UserName un

||| A smart constructor taking a string and parsing it as the appropriate
||| username
export
mkUserName : String -> UserName
mkUserName "_" = Underscore
mkUserName str with (strM str)
  mkUserName _   | StrCons '.' n = Field n
  mkUserName str | _             = Basic str

||| Name helps us track a name's structure as well as its origin:
||| was it user-provided or machine-manufactured? For what reason?
public export
data Name : Type where
     NS : Namespace -> Name -> Name -- in a namespace
     UN : UserName -> Name -- user defined name
     MN : String -> Bits32 -> Name -- machine generated name
     PV : Name -> Bits32 -> Name -- pattern variable name; int is the resolved function id
     DN : String -> Name -> Name -- a name and how to display it
     Nested : (Bits32, Bits32) -> Name -> Name -- nested function name
     CaseBlock : String -> Bits32 -> Name -- case block nested in (resolved) name
     WithBlock : String -> Bits32 -> Name -- with block nested in (resolved) name
     Resolved : Bits32 -> Name -- resolved, index into context

%runElab derive "IRW.Core.Name.Name" [Show,Eq,Ord]

%name Name n

export
mkNamespacedName : Maybe Namespace -> UserName -> Name
mkNamespacedName Nothing nm = UN nm
mkNamespacedName (Just ns) nm = NS ns (UN nm)

||| `matches a b` checks that the name `a` matches `b` assuming
||| the name roots are already known to be matching.
||| For instance, both `reverse` and `List.reverse` match the fully
||| qualified name `Data.List.reverse`.
export
matches : Name -> Name -> Bool
matches (NS ns _) (NS cns _) = isApproximationOf ns cns
matches _         _          = True

-- Update a name imported with 'import as', for creating an alias
export
asName :
     ModuleIdent -- Initial module name
  -> Namespace -- 'as' module name
  -> Name -- identifier
  -> Name
asName old new (DN s n)  = DN s (asName old new n)
asName old new (NS ns n) = NS (replace old new ns) n
asName _   _   n         = n

export
userNameRoot : Name -> Maybe UserName
userNameRoot (NS _ n) = userNameRoot n
userNameRoot (UN n) = Just n
userNameRoot (DN _ n) = userNameRoot n
userNameRoot _ = Nothing

opchars : List Char
opchars = unpack ":!#$%&*+./<=>?@\\^|-~"

export %inline
isOpChar : Char -> Bool
isOpChar c = c `elem` opchars

||| Test whether a user name begins with an operator symbol.
export
isOpUserName : UserName -> Bool
isOpUserName (Basic n)  = maybe False (isOpChar . fst) $ strUncons n
isOpUserName (Field _)  = False
isOpUserName Underscore = False

export
||| Test whether a name begins with an operator symbol.
isOpName : Name -> Bool
isOpName = maybe False isOpUserName . userNameRoot

export
isUnderscoreName : Name -> Bool
isUnderscoreName (UN Underscore) = True
isUnderscoreName (MN "_" _) = True
isUnderscoreName _ = False

export
isPatternVariable : UserName -> Bool
isPatternVariable (Basic nm) = lowerFirst nm
isPatternVariable (Field _) = False
isPatternVariable Underscore = True

export
isUserName : Name -> Bool
isUserName (PV {}) = False
isUserName (MN {}) = False
isUserName (NS _ n) = isUserName n
isUserName (DN _ n) = isUserName n
isUserName _ = True

||| True iff name can be traced back to a source name.
||| Used to determine whether it needs semantic highlighting.
export
isSourceName : Name -> Bool
isSourceName (NS _ n) = isSourceName n
isSourceName (UN {}) = True
isSourceName (MN {}) = False
isSourceName (PV n _) = isSourceName n
isSourceName (DN _ n) = isSourceName n
isSourceName (Nested _ n) = isSourceName n
isSourceName (CaseBlock {}) = False
isSourceName (WithBlock {}) = False
isSourceName (Resolved {}) = False

export
isRF : Name -> Maybe (Namespace, String)
isRF (NS ns n) = mapFst (ns <+>) <$> isRF n
isRF (UN (Field n)) = Just (emptyNS, n)
isRF _ = Nothing

export
isUN : Name -> Maybe (Namespace, UserName)
isUN (UN un) = Just (emptyNS, un)
isUN (NS ns n) = mapFst (ns <+>) <$> isUN n
isUN _ = Nothing

export
isBasic : UserName -> Maybe String
isBasic (Basic str) = Just str
isBasic _ = Nothing

export
isField : UserName -> Maybe String
isField (Field str) = Just str
isField _ = Nothing

export
caseFn : Name -> Bool
caseFn (CaseBlock {}) = True
caseFn (DN _ n) = caseFn n
caseFn (NS _ n) = caseFn n
caseFn _ = False

export
displayUserName : UserName -> String
displayUserName (Basic n) = n
displayUserName (Field n) = n
displayUserName Underscore = "_"

export
nameRoot : Name -> String
nameRoot (NS _ n) = nameRoot n
nameRoot (UN n) = displayUserName n
nameRoot (MN n _) = n
nameRoot (PV n _) = nameRoot n
nameRoot (DN _ n) = nameRoot n
nameRoot (Nested _ inner) = nameRoot inner
nameRoot (CaseBlock n _) = "$" ++ show n
nameRoot (WithBlock n _) = "$" ++ show n
nameRoot (Resolved i) = "$" ++ show i

export
displayName : Name -> (Maybe Namespace, String)
displayName (NS ns n) = mapFst (pure . maybe ns (ns <+>)) $ displayName n
displayName (UN n) = (Nothing, displayUserName n)
displayName (MN n _) = (Nothing, n)
displayName (PV n _) = displayName n
displayName (DN n _) = (Nothing, n)
displayName (Nested _ n) = displayName n
displayName (CaseBlock outer _) = (Nothing, "case block in " ++ show outer)
displayName (WithBlock outer _) = (Nothing, "with block in " ++ show outer)
displayName (Resolved i) = (Nothing, "$resolved" ++ show i)

export
splitNS : Name -> (Namespace, Name)
splitNS (NS ns nm) = mapFst (ns <+>) (splitNS nm)
splitNS nm = (emptyNS, nm)

--- Drop a namespace from a name
export
dropNS : Name -> Name
dropNS (NS _ n) = n
dropNS n = n

-- Drop all of the namespaces from a name
export
dropAllNS : Name -> Name
dropAllNS (NS _ n) = dropAllNS n
dropAllNS n = n

export
mbApplyNS : Maybe Namespace -> Name -> Name
mbApplyNS Nothing n = n
mbApplyNS (Just ns) n = NS ns n

unsafeBuiltins : List String
unsafeBuiltins =
  ["prim__believe_me", "believe_me", "prim__crash", "idris_crash"]

export
isUnsafeBuiltin : Name -> Bool
isUnsafeBuiltin nm = case splitNS nm of
  (ns, UN (Basic str)) =>
       (ns == builtinNS || ns == emptyNS)
    && (("assert_" `isPrefixOf` str) || (str `elem` unsafeBuiltins))
  _ => False

export
Interpolation UserName where
  interpolate (Basic n) = n
  interpolate (Field n) = "." ++ n
  interpolate Underscore = "_"

%inline
Interpolation Bits32 where interpolate = show

export
Interpolation Name where
  interpolate (NS ns n@(UN (Field _))) = "\{ns}.(\{n})"
  interpolate (NS ns (UN (Basic n))) =
    if any isOpChar (unpack n) then "\{ns}.(\{n})" else "\{ns}.\{n}"
  interpolate (NS ns n) = "\{ns}.\{n}"
  interpolate (UN x) = interpolate x
  interpolate (MN x y) = "{\{x}:\{y}}"
  interpolate (PV n d) = "{P:\{n}:\{d}}"
  interpolate (DN str n) = str
  interpolate (Nested (outer, idx) inner) = "\{outer}:\{idx}:\{inner}"
  interpolate (CaseBlock outer i) = "case block in " ++ outer
  interpolate (WithBlock outer i) = "with block in " ++ outer
  interpolate (Resolved x) = "$resolved\{x}"

export
HDecEq UserName where
  hdecEq (Basic x)  (Basic y)  = M0.maybeCong Basic (hdecEq x y)
  hdecEq (Field x)  (Field y)  = M0.maybeCong Field (hdecEq x y)
  hdecEq Underscore Underscore = Just0 Refl
  hdecEq _ _                   = Nothing0

export
HDecEq Name where
  hdecEq (NS xs x) (NS ys y) = M0.maybeCong2 NS (hdecEq xs ys) (hdecEq x y)
  hdecEq (UN x) (UN y) = M0.maybeCong UN (hdecEq x y)
  hdecEq (MN x t) (MN x' t') = M0.maybeCong2 MN (hdecEq x x') (hdecEq t t')
  hdecEq (PV x t) (PV y t') = M0.maybeCong2 PV (hdecEq x y) (hdecEq t t')
  hdecEq (DN x t) (DN y t') = M0.maybeCong2 DN (hdecEq x y) (hdecEq t t')
  hdecEq (Nested x y) (Nested x' y') = M0.maybeCong2 Nested (hdecEq x x') (hdecEq y y')
  hdecEq (CaseBlock x y) (CaseBlock x' y') = M0.maybeCong2 CaseBlock (hdecEq x x') (hdecEq y y')
  hdecEq (WithBlock x y) (WithBlock x' y') = M0.maybeCong2 WithBlock (hdecEq x x') (hdecEq y y')
  hdecEq (Resolved x) (Resolved y) = M0.maybeCong Resolved (hdecEq x y)
  hdecEq _ _ = Nothing0

||| Generate the next machine name
export
next : Name -> Name
next (MN n i) = MN n (i + 1)
next (UN n) = MN (interpolate n) 0
next (NS ns n) = NS ns (next n)
next n = MN (interpolate n) 0

-- levenstein distance that needs to be reached in order for a
-- namespace path to closely match another one.
closeNamespaceDistance : Nat
closeNamespaceDistance = 3

-- Check if two strings are close enough to be similar, using the namespace
-- distance criteria.
closeDistance : String -> String -> Bool
closeDistance s1 s2 = D.compute s1 s2 < closeNamespaceDistance

basicString : Name -> SnocList String -> SnocList String
basicString n sn = maybe sn (sn:<) (isUN n >>= isBasic . snd)

||| Check if the test closely match the reference.
||| We only check for namespaces and user-defined names.
export
closeMatch : (test, reference : Name) -> Bool
closeMatch (NS pt nt) (NS pref nref) =
 let unfoldedTest := basicString nt pt.names
     unfoldedRef  := basicString nref pref.names
     tests        := zipWith D.compute unfoldedTest unfoldedRef
  in sum tests <= closeNamespaceDistance
closeMatch (UN (Basic test)) (UN (Basic ref)) = closeDistance test ref
closeMatch _ _ = False
