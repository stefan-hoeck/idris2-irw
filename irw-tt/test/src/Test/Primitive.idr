module Test.Primitive

import Data.List.Quantifiers
import Decidable.HDecEq
import Gen.TT

%default total

prop_primType_eq : Property
prop_primType_eq =
  property $ do
    [x,y] <- forAll $ hlist [primTypes, primTypes]
    case hdecEq x y of
      Just0 _  => x === y
      Nothing0 => x /== y

export
props : Group
props =
  MkGroup "IRW.Core.TT.Primitive"
    [ ("prop_primType_eq", prop_primType_eq)
    ]

