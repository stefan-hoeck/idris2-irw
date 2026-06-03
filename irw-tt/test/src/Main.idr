module Main

import Hedgehog
import Test.Primitive
import Test.Term

%default total

main : IO ()
main =
  test
    [ Primitive.props
    , Term.props
    ]
