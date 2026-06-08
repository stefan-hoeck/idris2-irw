module Test.Term

import Property.Eq
import Gen.TT

%default total

sc : Scope
sc = [<"x","y","z"]

prop_term_eqRefl : Property
prop_term_eqRefl = eqRefl (terms fullNames sc)

prop_term_eqSym : Property
prop_term_eqSym = eqSym (terms fullNames sc)

prop_term_eqTrans : Property
prop_term_eqTrans = eqTrans (terms fullNames sc)

export
props : Group
props =
  MkGroup "IRW.Core.TT.Primitive"
    [ ("prop_term_eqRefl", prop_term_eqRefl)
    , ("prop_term_eqSym", prop_term_eqSym)
    , ("prop_term_eqTrans", prop_term_eqTrans)
    ]


