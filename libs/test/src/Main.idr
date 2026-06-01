module Main

import Hedgehog
import Test.Libs.Text.Distance.Levenshtein

%default total

main : IO ()
main =
  test
    [ Levenshtein.props
    ]
