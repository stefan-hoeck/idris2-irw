module IRW.Libs.Data.Matrix1

import Data.Array.Core
import Data.Array.Mutable

%default total

--------------------------------------------------------------------------------
-- Lemmata
--------------------------------------------------------------------------------

0 matrixLemma : (x : Fin w) -> (y : Fin h) -> LT (finToNat x * h + finToNat y) (w * h)
matrixLemma _ _ = believe_me Z -- TODO

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| A linear, mutable `w*h` matrix holding values of type `a`.
export
record Matrix1 s (w,h : Nat) a where
  constructor M1
  content : MArray s (w * h) a

toPos : {h : _} -> Fin w -> Fin h -> Fin (w*h)
toPos i j = natToFinLT (finToNat i * h + finToNat j) @{matrixLemma i j}

export
newM1 : (w, h : Nat) -> a -> F1 s (Matrix1 s w h a)
newM1 w h v t = let m # t := marray1 (w * h) v t in M1 m # t

export %inline
writeM1 : {h : _} -> Matrix1 s w h a -> Fin w -> Fin h -> a -> F1' s
writeM1 (M1 c) x y = set c (toPos x y)

export %inline
readM1 : {h : _} -> Matrix1 s w h a -> Fin w -> Fin h -> F1 s a
readM1 (M1 c) x y = get c (toPos x y)
