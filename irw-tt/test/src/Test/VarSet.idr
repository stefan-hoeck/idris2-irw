module Test.VarSet

import IRW.Core.TT
import IRW.Core.TT.VarSet
import Gen.TT

%default total

prop_singleton : Property
prop_singleton =
  property $ do
    AV _ v <- forAll anyVars
    assert $ elem v (singleton v)

prop_insert : Property
prop_insert =
  property $ do
    AVS (ns:<n) set <- forAll anyVarSet | _ => pure ()
    v               <- forAll $ vars1 ns n
    assert $ elem v (insert v set)

prop_delete : Property
prop_delete =
  property $ do
    AVS (ns:<n) set <- forAll anyVarSet | _ => pure ()
    v               <- forAll $ vars1 ns n
    assert $ not $ elem v (delete v set)

prop_toList : Property
prop_toList =
  property $ do
    AVS ns set <- forAll anyVarSet
    unsafeToList set === toList set

export
props : Group
props =
  MkGroup "IRW.Core.TT.VarSet"
    [ ("prop_singleton", prop_singleton)
    , ("prop_insert", prop_insert)
    , ("prop_delete", prop_delete)
    , ("prop_toList", prop_toList)
    ]
