module Test.Name

import Decidable.HDecEq
import Data.Maybe0
import Data.List.Quantifiers
import Gen.Name

%default total

prop_eq_self : Property
prop_eq_self =
  property $ forAll names >>= \n => n === n

prop_hdecEq_self : Property
prop_hdecEq_self =
  property $ do
    n <- forAll names
    case hdecEq n n of
      Just0 _  => pure ()
      Nothing0 => failWith Nothing "\{n} not equal to itself"

prop_hdecEq_eq : Property
prop_hdecEq_eq =
  property $ do
    [x,y] <- forAll $ hlist [names,names]
    case hdecEq x y of
      Just0 _  => x === y
      Nothing0 => x /== y

export
props : Group
props =
  MkGroup "IRW.Core.Name"
    [ ("prop_eq_self", prop_eq_self)
    , ("prop_hdecEq_self", prop_hdecEq_self)
    , ("prop_hdecEq_eq", prop_hdecEq_eq)
    ]
