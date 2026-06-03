module Test.Namespace

import Data.List.Quantifiers
import Gen.Name
import IRW.Libs.Data.String.Extra

%default total

%inline
FromString Namespace where fromString = mkNamespace

prop_mkNamespace : Property
prop_mkNamespace =
  property $ do
    ns <- forAll namespaces
    mkNamespace "\{ns}" === ns

prop_mkNamespacedIdent : Property
prop_mkNamespacedIdent =
  property $ do
    [ns,i] <- forAll $ hlist [namespaces, identifiers]
    case ns.names of
      [<] => mkNamespacedIdent i === (Nothing,i)
      xs  => mkNamespacedIdent (snocSep "." $ xs:<i) === (Just ns,i)

prop_allParents : Property
prop_allParents =
  property $ do
    ns <- forAll namespaces
    assert $ all (`isParentOf` ns) (allParents ns)

prop_allParentsSize : Property
prop_allParentsSize =
  property $ do
    ns <- forAll namespaces
    length (allParents ns) === length ns.names

prop_isApproximationOf : Property
prop_isApproximationOf =
  property1 $ Prelude.do
    assert $ isApproximationOf "List.Properties" "Data.List.Properties"
    assert $ not $ isApproximationOf "Data.List.Properties" "List.Properties"

export
props : Group
props =
  MkGroup "IRW.Core.Name.Namespace"
    [ ("prop_mkNamespace", prop_mkNamespace)
    , ("prop_mkNamespacedIdent", prop_mkNamespacedIdent)
    , ("prop_allParents", prop_allParents)
    , ("prop_allParentsSize", prop_allParentsSize)
    , ("prop_isApproximationOf", prop_isApproximationOf)
    ]
