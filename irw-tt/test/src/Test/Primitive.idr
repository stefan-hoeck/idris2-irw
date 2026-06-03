module Test.Primitive

import Property.HDecEq
import Gen.TT

%default total

prop_primType_eq : Property
prop_primType_eq = hdecEqLaw primTypes

prop_constant_eq : Property
prop_constant_eq = hdecEqLaw constantsNoDb

export
props : Group
props =
  MkGroup "IRW.Core.TT.Primitive"
    [ ("prop_primType_eq", prop_primType_eq)
    , ("prop_constant_eq", prop_constant_eq)
    ]

