module Main

import Test.Namespace
import Hedgehog

%default total

main : IO ()
main =
  test
    [ Namespace.props
    ]
