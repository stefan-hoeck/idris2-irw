module Gen.Name

import public Hedgehog
import public IRW.Core.Name
import Data.Vect

%default total

export %inline
FromString Namespace where
  fromString = mkNamespace

export %inline
FromString RefName where
  fromString = refName

export
FromString FullName where
  fromString s =
    case mkNamespacedIdent s of
      (m,y) => FN m $ fromString y

||| Alpha-numeric, underscore ('_'), or single quote ('\'')
export
identChar : Gen Char
identChar = frequency [(58, alphaNum), (2, element ['_', '\''])]

||| Non-empty string starting with a letter followed by some
||| ident characters.
export
identifiers : Gen String
identifiers = fastPack <$> [| alpha :: list (linear 0 10) identChar |]

||| Like `identifiers` but always starts with a lower-case letter.
export
lcIdents : Gen String
lcIdents = fastPack <$> [| lower :: list (linear 0 10) identChar |]

export
varNames : Gen VarName
varNames = VN <$> identifiers

export
opChar : Gen Char
opChar =
  element
    [':','!','#','$','%','&','*','+','.','/'
    ,'<','=','>','?','@','\\','^','|','-','~'
    ]

export
opNames : Gen String
opNames = fastPack <$> [| opChar :: list (linear 0 4) opChar |]

||| Like `identifiers` but starts with an upper-case character.
export
moduleNames : Gen String
moduleNames = fastPack <$> [| upper :: list (linear 0 10) identChar |]

||| A snoc-list of module names.
export
namespaces : Gen Namespace
namespaces = MkNS <$> snocList (linear 0 4) moduleNames

||| A snoc-list of module names.
export
moduleIdents : Gen ModuleIdent
moduleIdents = MkMI <$> snocList (linear 0 4) moduleNames

||| A generator of `UserName`s
export
refNames : Gen RefName
refNames =
  choice
    [ Basic <$> identifiers
    , Field <$> lcIdents
    , Op <$> opNames
    ]
--
export %inline
fullNames : Gen FullName
fullNames = [| FN (maybe namespaces) refNames |]
