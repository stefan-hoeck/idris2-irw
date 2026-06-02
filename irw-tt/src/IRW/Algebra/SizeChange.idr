module IRW.Algebra.SizeChange

import Derive.Prelude
import IRW.Algebra.Semiring

%default total
%language ElabReflection

public export
data SizeChange = Unknown | Same | Smaller

%runElab derive "SizeChange" [Show,Eq,Ord]

export
Semigroup SizeChange where
  -- Same is a neutral
  Unknown <+> _ = Unknown
  Same <+> c = c
  _ <+> Unknown = Unknown
  Smaller <+> _ = Smaller

export
Monoid SizeChange where
  neutral = Same

export
Semiring SizeChange where
  (|*|) = (<+>)
  timesNeutral = neutral
  (|+|) Unknown y = y
  (|+|) Same Unknown = Same
  (|+|) Same y = y
  (|+|) Smaller y = Smaller
  plusNeutral = Unknown

-- semiring laws
scPlusNeutralLeft : (a : SizeChange) -> Unknown |+| a = a
scPlusNeutralLeft a = Refl

scPlusNeutralRight : (a : SizeChange) -> a |+| Unknown = a
scPlusNeutralRight Smaller = Refl
scPlusNeutralRight Same = Refl
scPlusNeutralRight Unknown = Refl

partial
scPlusCommutative : (a, b : SizeChange) -> a |+| b = b |+| a
scPlusCommutative Unknown b = sym (scPlusNeutralRight b)
scPlusCommutative b Unknown = scPlusNeutralRight b
scPlusCommutative Smaller Smaller = Refl
scPlusCommutative Same Smaller = Refl
scPlusCommutative Smaller Same = Refl
scPlusCommutative Same Same = Refl

scPlusAssoc : (a, b, c : SizeChange) -> (a |+| b) |+| c = a |+| (b |+| c)
scPlusAssoc Smaller b c = Refl
scPlusAssoc Same Smaller c = Refl
scPlusAssoc Same Same Smaller = Refl
scPlusAssoc Same Same Same = Refl
scPlusAssoc Same Same Unknown = Refl
scPlusAssoc Same Unknown c = Refl
scPlusAssoc Unknown b c = Refl

scMultNeutralLeft : (a : SizeChange) -> Same |*| a = a
scMultNeutralLeft a = Refl

scMultNeutralRight : (a : SizeChange) -> a |*| Same = a
scMultNeutralRight Smaller = Refl
scMultNeutralRight Same = Refl
scMultNeutralRight Unknown = Refl

scMultZeroLeft : (a : SizeChange) -> Unknown |*| a = Unknown
scMultZeroLeft a = Refl

scMultZeroRight : (a : SizeChange) -> a |*| Unknown = Unknown
scMultZeroRight Smaller = Refl
scMultZeroRight Same = Refl
scMultZeroRight Unknown = Refl

scMultAssociative : (a, b, c : SizeChange) -> a |*| (b |*| c) = (a |*| b) |*| c
scMultAssociative Smaller Smaller Smaller = Refl
scMultAssociative Same b c = Refl
scMultAssociative a Same c =
  rewrite scMultNeutralRight a in
  Refl
scMultAssociative a b Same =
  rewrite scMultNeutralRight b in
  rewrite scMultNeutralRight (a |*| b) in
  Refl
scMultAssociative Unknown b c = Refl
scMultAssociative a Unknown c =
  rewrite scMultZeroRight a in
  Refl
scMultAssociative a b Unknown =
  rewrite scMultZeroRight b in
  rewrite scMultZeroRight a in
  rewrite scMultZeroRight (a |*| b) in
  Refl

scMultCommutative : (a, b : SizeChange) -> a |*| b = b |*| a
scMultCommutative Smaller Smaller = Refl
scMultCommutative b Same =
  rewrite scMultNeutralRight b in
  Refl
scMultCommutative Smaller Unknown = Refl
scMultCommutative Same b =
  rewrite scMultNeutralRight b in
  Refl
scMultCommutative Unknown b =
 rewrite scMultZeroRight b in
 Refl

scPlusIdempotent : (a : SizeChange) -> a |+| a = a
scPlusIdempotent Smaller = Refl
scPlusIdempotent Same = Refl
scPlusIdempotent Unknown = Refl

scMultPlusDist : (a, b, c : SizeChange) -> a |*| (b |+| c) = (a |*| b) |+| (a |*| c)
scMultPlusDist Unknown b c = Refl
scMultPlusDist a Unknown c =
  rewrite scMultZeroRight a in
  Refl
scMultPlusDist a b Unknown =
  rewrite scPlusNeutralRight b in
  rewrite scMultZeroRight a in
  rewrite scPlusNeutralRight (a |*| b) in
  Refl
scMultPlusDist Same b c = Refl
scMultPlusDist a Same Same =
  rewrite scMultNeutralRight a in
  rewrite scPlusIdempotent a in
  Refl
scMultPlusDist Smaller Same Smaller = Refl
scMultPlusDist Smaller Smaller Same = Refl
scMultPlusDist Smaller Smaller Smaller = Refl

maxLaw : (a,b : SizeChange) -> max a b = a |+| b
maxLaw Unknown Unknown = Refl
maxLaw Unknown Same = Refl
maxLaw Unknown Smaller = Refl
maxLaw Same Unknown = Refl
maxLaw Same Same = Refl
maxLaw Same Smaller = Refl
maxLaw Smaller Unknown = Refl
maxLaw Smaller Same = Refl
maxLaw Smaller Smaller = Refl
