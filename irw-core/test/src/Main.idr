module Main

import Test.Name
import Test.Namespace
import Hedgehog

%default total

main : IO ()
main =
  test
    [ Name.props
    , Namespace.props
    ]
