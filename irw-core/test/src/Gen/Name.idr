module Gen.Name

import public Hedgehog
import public IRW.Core.Name
import Data.Vect

%default total

export %inline
FromString Namespace where
  fromString = mkNamespace

export %inline
FromString UserName where
  fromString = mkUserName

export
FromString Name where
  fromString s =
    case mkNamespacedIdent s of
      (Just ns,y) => NS ns (UN $ fromString y)
      (_,y)       => UN $ fromString y

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
userNames : Gen UserName
userNames =
  frequency
    [ (10, Basic <$> identifiers)
    , (10, Field <$> lcIdents)
    , (1, pure Underscore)
    ]

names0 : Gen Name
names0 =
  choice
    [ UN <$> userNames
    , [| MN (string (linear 1 4) lower) anyBits32 |]
    , [| PV (UN <$> userNames) anyBits32 |]
    , [| DN (string (linear 1 4) lower) (UN <$> userNames) |]
    , [| CaseBlock (string (linear 1 4) lower) anyBits32 |]
    , [| WithBlock (string (linear 1 4) lower) anyBits32 |]
    , [| Resolved anyBits32 |]
    ]

namesN : Nat -> Gen Name
namesN 0     = names0
namesN (S k) =
  choice $
    [ [| NS namespaces names0 |]
    , [| Nested [| (anyBits32, anyBits32) |] (namesN k) |]
    , names0
    ]

||| A generator of `Name`s
export %inline
names : Gen Name
names = namesN 2
