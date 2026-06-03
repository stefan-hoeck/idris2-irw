module Property.Eq

import public Data.List.Quantifiers
import public Hedgehog

%default total

export
eqRefl : Show a => Eq a => Gen a -> Property
eqRefl g =
  property $ do
    x <- forAll g
    x === x

export
eqSym : Show a => Eq a => Gen a -> Property
eqSym g =
  property $ do
    [x,y] <- forAll $ hlist [g,g]
    (x == y) === (y == x)

export
eqTrans : Show a => Eq a => Gen a -> Property
eqTrans g =
  property $ do
    [x,y,z] <- forAll $ hlist [g,g,g]
    case x == y  && y == z of
      False => pure ()
      True  => x === z
