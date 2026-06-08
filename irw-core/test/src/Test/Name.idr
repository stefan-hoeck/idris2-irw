module Test.Name

import Property.HDecEq
import Gen.Name

%default total

prop_eq_self : Property
prop_eq_self =
  property $ forAll fullNames >>= \n => n === n

prop_hdecEq_self : Property
prop_hdecEq_self =
  property $ do
    n <- forAll fullNames
    case hdecEq n n of
      Just0 _  => pure ()
      Nothing0 => failWith Nothing "\{n} not equal to itself"

prop_hdecEq_eq : Property
prop_hdecEq_eq = hdecEqLaw fullNames

export
props : Group
props =
  MkGroup "IRW.Core.Name"
    [ ("prop_eq_self", prop_eq_self)
    , ("prop_hdecEq_self", prop_hdecEq_self)
    , ("prop_hdecEq_eq", prop_hdecEq_eq)
    ]
