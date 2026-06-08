module IRW.Core.Name

import Data.Maybe0 as M0
import Data.SnocList
import Data.SortedMap
import Decidable.HDecEq
import Derive.Prelude
import IRW.Libs.Data.String.Extra
import IRW.Libs.Text.Distance.Levenshtein as D

import public IRW.Core.Name.Namespace

%default total
%language ElabReflection

%hide Language.Reflection.TT.ModuleIdent
%hide Language.Reflection.TT.Namespace

public export
record VarName where
  constructor VN
  name : String

%runElab derive "VarName" [Show,Eq,Ord,FromString]

export
machineName : String -> Nat -> VarName
machineName s n = VN "\{s}_\{show n}"

export %inline
Interpolation VarName where interpolate = name

export
HDecEq VarName where
  hdecEq (VN x) (VN y) = M0.maybeCong VN (hdecEq x y)

public export
data RefName : Type where
  Basic : String -> RefName -- default name constructor       e.g. map
  Op    : String -> RefName
  Field : String -> RefName -- field accessor                 e.g. .fst

%runElab derive "RefName" [Show,Eq,Ord]

export
Interpolation RefName where
  interpolate (Basic n) = n
  interpolate (Op n)    = n
  interpolate (Field n) = "." ++ n

opchars : List Char
opchars = unpack ":!#$%&*+./<=>?@\\^|-~"

export %inline
isOpChar : Char -> Bool
isOpChar c = c `elem` opchars

||| A smart constructor taking a string and parsing it as the appropriate
||| username
export
refName : String -> RefName
refName s  =
  case strM s of
    StrCons '.' n => Field n
    StrCons x   n => if isOpChar x then Op s else Basic s
    _             => Basic s

public export
record FullName where
  constructor FN
  namesp : Maybe Namespace
  ref    : RefName

%runElab derive "FullName" [Show,Eq,Ord]

export
Interpolation FullName where
  interpolate (FN Nothing n) = interpolate n
  interpolate (FN (Just ns) $ Op n) = "\{ns}.(\{n})"
  interpolate (FN (Just ns) $ Basic n) = "\{ns}.\{n}"
  interpolate (FN (Just ns) $ Field n) = "\{ns}.(\{n})"

export
toVarName : FullName -> Maybe VarName
toVarName (FN Nothing $ Basic s) = Just (VN s)
toVarName _                      = Nothing

-- export
-- isPatternVariable : UserName -> Bool
-- isPatternVariable (Basic nm) = lowerFirst nm
-- isPatternVariable (Field _) = False
-- isPatternVariable Underscore = True

-- unsafeBuiltins : List String
-- unsafeBuiltins =
--   ["prim__believe_me", "believe_me", "prim__crash", "idris_crash"]
--
-- export
-- isUnsafeBuiltin : Name -> Bool
-- isUnsafeBuiltin nm = case splitNS nm of
--   (ns, UN (Basic str)) =>
--        (ns == builtinNS || ns == emptyNS)
--     && (("assert_" `isPrefixOf` str) || (str `elem` unsafeBuiltins))
--   _ => False

-- -- levenstein distance that needs to be reached in order for a
-- -- namespace path to closely match another one.
-- closeNamespaceDistance : Nat
-- closeNamespaceDistance = 3
--
-- -- Check if two strings are close enough to be similar, using the namespace
-- -- distance criteria.
-- closeDistance : String -> String -> Bool
-- closeDistance s1 s2 = D.compute s1 s2 < closeNamespaceDistance
--
-- basicString : Name -> SnocList String -> SnocList String
-- basicString n sn = maybe sn (sn:<) (isUN n >>= isBasic . snd)
--
-- ||| Check if the test closely match the reference.
-- ||| We only check for namespaces and user-defined names.
-- export
-- closeMatch : (test, reference : Name) -> Bool
-- closeMatch (NS pt nt) (NS pref nref) =
--  let unfoldedTest := basicString nt pt.names
--      unfoldedRef  := basicString nref pref.names
--      tests        := zipWith D.compute unfoldedTest unfoldedRef
--   in sum tests <= closeNamespaceDistance
-- closeMatch (UN (Basic test)) (UN (Basic ref)) = closeDistance test ref
-- closeMatch _ _ = False
