module Property.HDecEq

import public Data.List.Quantifiers
import public Decidable.HDecEq
import public Hedgehog

%default total

export
hdecEqLaw : Show a => Eq a => HDecEq a => Gen a -> Property
hdecEqLaw g =
  property $ do
    [x,y] <- forAll $ hlist [g, g]
    case hdecEq x y of
      Just0 _  => x === y
      Nothing0 => x /== y
