module Gen.Name

import public Hedgehog
import public IRW.Core.Name
import Data.Vect

%default total

export
identChar : Gen Char
identChar = frequency [(58, alphaNum), (2, element ['_', '\''])]

export
identifiers : Gen String
identifiers = fastPack <$> [| alpha :: list (linear 0 10) identChar |]

export
moduleNames : Gen String
moduleNames = fastPack <$> [| upper :: list (linear 0 10) identChar |]

export
namespaces : Gen Namespace
namespaces = MkNS <$> snocList (linear 0 4) moduleNames

export
moduleIdents : Gen ModuleIdent
moduleIdents = MkMI <$> snocList (linear 0 4) moduleNames
