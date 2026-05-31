module Test.Libs.Text.Distance.Levenshtein

import Data.List
import Data.List.Quantifiers
import Data.String
import Hedgehog
import IRW.Libs.Text.Distance.Levenshtein

%default total

str : Gen String
str = string (linear 0 10) unicode

cost : Char -> Char -> Nat
cost c d =
  if c == d                 then 0 else
  if isAlpha c && isAlpha d then 1 else
  if isDigit c && isDigit d then 1 else 2

-- Self-evidently correct but O(3 ^ (min mn)) complexity
spec : String -> String -> Nat
spec a b = loop (fastUnpack a) (fastUnpack b)
  where
    loop : List Char -> List Char -> Nat
    loop [] ys = length ys -- deletions
    loop xs [] = length xs -- insertions
    loop (x :: xs) (y :: ys) =
      case x == y of
        True  => loop xs ys
        False => 
          min
            (1 + loop (x :: xs) ys)
            (min (1 + loop xs (y :: ys)) (cost x y + loop xs ys))

prop_self : Property
prop_self =
  property $ Prelude.do
    s <- forAll str
    compute s s === 0

prop_spec : Property
prop_spec =
  property $ Prelude.do
    [s1,s2] <- forAll $ hlist [str,str]
    compute s1 s2 === spec s1 s2

export
props : Group
props =
  MkGroup "IRW.Libs.Text.Distance.Levenshtein"
    [ ("prop_self", prop_self)
    , ("prop_spec", prop_spec)
    ]
