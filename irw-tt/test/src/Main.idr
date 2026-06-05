module Main

import Hedgehog
import Test.Primitive
import Test.Term
import Test.VarSet

%default total

main : IO ()
main =
  test
    [ Primitive.props
    , Term.props
    , VarSet.props
    ]
