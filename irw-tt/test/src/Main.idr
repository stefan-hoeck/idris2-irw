module Main

import Hedgehog
import Test.Primitive

%default total

main : IO ()
main =
  test
    [ Primitive.props
    ]
