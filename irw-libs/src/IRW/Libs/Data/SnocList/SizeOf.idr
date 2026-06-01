module IRW.Libs.Data.SnocList.SizeOf

import Data.Nat
import public Data.SnocList
import public Data.SnocList.HasLength

%default total

public export
record SizeOf {a : Type} (sx : SnocList a) where
  constructor MkSizeOf
  size        : Nat
  0 hasLength : HasLength size sx

export
0 theSnocList : SizeOf {a} sx -> SnocList a
theSnocList _ = sx

public export
zero : SizeOf [<]
zero = MkSizeOf Z Z

public export
suc : SizeOf sa -> SizeOf (sa:<a)
suc (MkSizeOf n p) = MkSizeOf (S n) (S p)

||| suc but from the right
export
sucL : SizeOf sa -> SizeOf ([<a] ++ sa)
sucL (MkSizeOf n p) = MkSizeOf (S n) (sucL p)

export
(+) : SizeOf sx -> SizeOf sy -> SizeOf (sx ++ sy)
MkSizeOf m p + MkSizeOf n q = MkSizeOf (n + m) (hlAppend p q)

export
mkSizeOf : (sx : SnocList a) -> SizeOf sx
mkSizeOf sx = MkSizeOf (length sx) (mkHasLength sx)

export
reverse : SizeOf sx -> SizeOf (reverse sx)
reverse (MkSizeOf n p) = MkSizeOf n (hlReverse p)

export
map : SizeOf sx -> SizeOf (map f sx)
map (MkSizeOf n p) = MkSizeOf n (map f p)

namespace SizedView

  public export
  data SizedView : SizeOf sa -> Type where
    Z : SizedView (MkSizeOf Z Z)
    S : (n : SizeOf sa) -> SizedView (suc {a} n)

export
sizedView : (p : SizeOf sa) -> SizedView p
sizedView (MkSizeOf Z Z)         = Z
sizedView (MkSizeOf (S n) (S p)) = S (MkSizeOf n p)
