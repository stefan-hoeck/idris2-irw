module IRW.Libs.Data.SnocList.SizeOf

import Data.Nat
import Data.List
import public Data.SnocList
import public Data.SnocList.HasLength
import public Data.List.HasLength as L

%default total

namespace SnocList
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

namespace List
  public export
  record LSizeOf {a : Type} (xs : List a) where
    constructor MkLSizeOf
    size        : Nat
    0 hasLength : HasLength size xs

  export
  0 theList : LSizeOf {a} xs -> List a
  theList _ = xs

  public export
  zero : LSizeOf []
  zero = MkLSizeOf Z Z

  public export
  suc : LSizeOf as -> LSizeOf (a :: as)
  suc (MkLSizeOf n p) = MkLSizeOf (S n) (S p)

  -- ||| suc but from the right
  export
  sucR : LSizeOf as -> LSizeOf (as ++ [a])
  sucR (MkLSizeOf n p) = MkLSizeOf (S n) (sucR p)

  export
  (+) : LSizeOf xs -> LSizeOf ys -> LSizeOf (xs ++ ys)
  MkLSizeOf m p + MkLSizeOf n q = MkLSizeOf (m + n) (hasLengthAppend p q)

  export
  mkSizeOf : (xs : List a) -> LSizeOf xs
  mkSizeOf xs = MkLSizeOf (length xs) (hasLength xs)

  export
  reverse : LSizeOf xs -> LSizeOf (reverse xs)
  reverse (MkLSizeOf n p) = MkLSizeOf n (hasLengthReverse p)

  cast : {ys : _} -> (0 _ : List.length xs = List.length ys) -> L.HasLength m xs -> L.HasLength m ys
  cast {ys = []}      eq Z = Z
  cast {ys = y :: ys} eq (S p) = S (cast (injective eq) p)

  export
  map : LSizeOf xs -> LSizeOf (map f xs)
  map (MkLSizeOf n p) = MkLSizeOf n (cast (sym $ lengthMap xs) p)

  export
  take : {n : Nat} -> {0 xs : Stream a} -> LSizeOf (take n xs)
  take = MkLSizeOf n (take n xs)

  export
  (<><) : SizeOf sx -> LSizeOf xs -> SizeOf (sx<><xs)
  (<><) (MkSizeOf x hx) (MkLSizeOf y hy) = MkSizeOf (y+x) (hlFish hx hy)

