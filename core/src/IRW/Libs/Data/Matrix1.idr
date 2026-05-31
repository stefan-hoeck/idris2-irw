module IRW.Libs.Data.Matrix1

import Data.Linear.Traverse1
import Data.Array.Core
import Data.Array.Mutable
import Syntax.T1

%default total

||| A linear, mutable `w*h` matrix holding values of type `a`.
public export
0 Matrix1 : Type -> (w,h : Nat) -> Type -> Type
Matrix1 s w h a = MArray s w (MArray s h a)

export
newM1 : (w, h : Nat) -> a -> F1 s (Matrix1 s w h a)
newM1 w h v = T1.do
  m <- unsafeMArray1 {a = MArray s h a} w
  for1_ (allFinsFast w) $ \i => marray1 h v >>= set m i
  pure m

export %inline
writeM1 : Matrix1 s w h a -> Fin w -> Fin h -> a -> F1' s
writeM1 m x y v t = let r # t := get m x t in set r y v t

export %inline
readM1 : Matrix1 s w h a -> Fin w -> Fin h -> F1 s a
readM1 m x y t = let r # t := get m x t in get r y t
