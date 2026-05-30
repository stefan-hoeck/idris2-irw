module IRW.Libs.Data.Matrix1

import Data.Array.Core
import Data.Array.Mutable

%default total

--------------------------------------------------------------------------------
-- Lemmata
--------------------------------------------------------------------------------

0 multLemma : LT 0 (S w * S h)
multLemma = LTESucc LTEZero

0 plusLT : LT x y -> LT m n -> LT (plus x m) (plus y n)
plusLT {x = 0}             _           lt = transitive lt (lteAddLeft _)
plusLT {x = S a} {y = S b} (LTESucc l) lt = LTESucc $ plusLT l lt

0 matrixLemma : (x : Fin w) -> (y : Fin h) -> LT (finToNat x * finToNat y) (w * h)
matrixLemma FZ     FZ     = multLemma
matrixLemma FZ     (FS x) = multLemma
matrixLemma (FS x) y      = plusLT (finToNatLT _) $ matrixLemma x y

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| A linear, mutable `w*h` matrix holding values of type `a`.
export
record Matrix1 s (w,h : Nat) a where
  constructor M1
  content : MArray s (w * h) a

export
newM1 : (w, h : Nat) -> a -> F1 s (Matrix1 s w h a)
newM1 w h v t = let m # t := marray1 (w * h) v t in M1 m # t

export
writeM1 : Matrix1 s w h a -> Fin w -> Fin h -> a -> F1' s
writeM1 (M1 c) x y v t =
  setNat c (finToNat x * finToNat y) {lt = matrixLemma x y} v t

export
readM1 : Matrix1 s w h a -> Fin w -> Fin h -> F1 s a
readM1 (M1 c) x y t =
  getNat c (finToNat x * finToNat y) {lt = matrixLemma x y} t
