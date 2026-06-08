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

prop_weaken : Property
prop_weaken =
  property $ do
    AVS (ns:<n) set <- forAll anyVarSet | _ => pure ()
    v               <- forAll $ vars1 ns n
    elem v set === elem (weaken v) (weaken {nm = "Foo"} set)

prop_weakenNs : Property
prop_weakenNs =
  property $ do
    AVS (ns:<n) set <- forAll anyVarSet | _ => pure ()
    v               <- forAll $ vars1 ns n
    sn              <- forAll $ snocList (linear 0 10) varNames
    let sz := mkSizeOf sn
    elem v set === elem (weakenNs sz v) (weakenNs sz set)

prop_genWeakenNs : Property
prop_genWeakenNs =
  property $ do
    AVS outer set <- forAll anyVarSet
    local         <- forAll $ snocList (linear 0 10) varNames
    ns            <- forAll $ snocList (linear 0 10) varNames
    let Just g    := vars (outer++local) | Nothing => pure ()
    v             <- forAll g

    let sloc      := mkSizeOf local
        sns       := mkSizeOf ns
        set2      := insert v $ weakenNs sloc set

    assert $ elem (genWeakenNs sloc sns v) (genWeakenNs sloc sns set2)

export
props : Group
props =
  MkGroup "IRW.Core.TT.VarSet"
    [ ("prop_singleton", prop_singleton)
    , ("prop_insert", prop_insert)
    , ("prop_delete", prop_delete)
    , ("prop_toList", prop_toList)
    , ("prop_weaken", prop_weaken)
    , ("prop_weakenNs", prop_weakenNs)
    , ("prop_genWeakenNs", prop_genWeakenNs)
    ]
