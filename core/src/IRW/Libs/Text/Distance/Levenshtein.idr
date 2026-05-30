module IRW.Libs.Text.Distance.Levenshtein

import Data.Linear.Traverse1
import Data.Array.Index
import Data.String
import IRW.Libs.Data.Matrix1
import Syntax.T1

%default total

-- TODO: This should go to idris2-array and replace the one from indexed-graph
||| Generates the list of all `Fin n` in linear type.
|||
||| This is a lot faster than `Data.Fin.allFins`, which runs in quadratic
||| time.
export
allFinsFast : (n : Nat) -> List (Fin n)
allFinsFast 0 = []
allFinsFast (S n) = go [] last
  where
    go : List (Fin $ S n) -> Fin (S n) -> List (Fin $ S n)
    go xs FZ     = FZ :: xs
    go xs (FS x) = go (FS x :: xs) (assert_smaller (FS x) $ weaken x)

-- Self-evidently correct but O(3 ^ (min mn)) complexity
-- TODO: this should be a test
spec : String -> String -> Nat
spec a b = loop (fastUnpack a) (fastUnpack b) where

  loop : List Char -> List Char -> Nat
  loop [] ys = length ys -- deletions
  loop xs [] = length xs -- insertions
  loop (x :: xs) (y :: ys)
    = if x == y then loop xs ys -- match
      else 1 + minimum
           [ loop (x :: xs) ys -- insert y
           , loop xs (y :: ys) -- delete x
           , loop xs ys        -- substitute y for x
           ]

LenS : (s : String) -> Nat
LenS s = cast $ strLength s

%inline
sfins : (s : String) -> List (Fin (S $ LenS s))
sfins s = allFinsFast (S $ LenS s)

%inline
fins : (s : String) -> List (Fin $ LenS s)
fins s = allFinsFast (LenS s)

%inline
six : (s : String) -> Fin (LenS s) -> Char
six s n = assert_total $ strIndex s (cast $ finToNat n)

-- here we change Levenshtein slightly so that we may only substitute
-- alpha / numerical characters for similar ones. This avoids suggesting
-- "#" as a replacement for an out of scope "n".
cost : Char -> Char -> Nat
cost c d =
  if c == d                 then 0 else
  if isAlpha c && isAlpha d then 1 else
  if isDigit c && isDigit d then 1 else 2

-- Dynamic programming
compute1 : String -> String -> F1 s Nat
compute1 s1 s2 = T1.do
  -- In mat[i][j], we store the distance between
  -- * the suffix of a of size i
  -- * the suffix of b of size j
  -- So we need a matrix of size (|a|+1) * (|b|+1)
  mat <- newM1 (S $ LenS s1) (S $ LenS s2) Z
  -- Whenever one of the two suffixes of interest is empty, the only
  -- winning move is to:
  -- * delete all of the first
  -- * insert all of the second
  -- i.e. the cost is the length of the non-zero suffix
  for1_ (sfins s1) $ \i => writeM1 mat i 0 (finToNat i)
  for1_ (sfins s2) $ \j => writeM1 mat 0 j (finToNat j)
  for1_ (fins s2) $ \j => for1_ (fins s1) $ \i => T1.do
    ij1  <- readM1 mat (FS i) (weaken j)
    i1j  <- readM1 mat (weaken i) (FS j)
    i1j1 <- readM1 mat (weaken i) (weaken j)
    let v := min (S ij1) (min (S i1j) $ cost (six s1 i) (six s2 j) + i1j1)
    writeM1 mat (FS i) (FS j) v
  -- Once the matrix is fully filled, we can simply read the top right corner
  readM1 mat last last

export
compute : String -> String -> Nat
compute x y = run1 (compute1 x y)
