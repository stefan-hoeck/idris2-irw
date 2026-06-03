module Gen.TT

import Data.Vect
import public Gen.Name
import public IRW.Algebra
import public IRW.Core.Name.Scoped
import public IRW.Core.TT.Binder
import public IRW.Core.TT.Primitive
import public IRW.Core.TT.Term
import public IRW.Core.TT.Var

%default total

public export
record AnyVar where
  constructor AV
  scope : Scope
  var   : Var scope

export
rigCounts : Gen ZeroOneOmega
rigCounts = element [erased,linear,top]

export
vars : (vs : Scope) -> Gen (Maybe $ Var vs)
vars vs =
  case allVars vs <>> [] of
    [] => pure Nothing
    h::t => Just <$> element (h :: fromList t)

--------------------------------------------------------------------------------
-- Primitives and Constants
--------------------------------------------------------------------------------

export
primTypes : Gen PrimType
primTypes =
  element
    [ IntType
    , Int8Type
    , Int16Type
    , Int32Type
    , Int64Type
    , IntegerType
    , Bits8Type
    , Bits16Type
    , Bits32Type
    , Bits64Type
    , StringType
    , CharType
    , DoubleType
    , WorldType
    ]

export
constants : Gen Constant
constants =
  choice
    [ (I . cast) <$> anyInt32
    , I8  <$> anyInt8
    , I16 <$> anyInt16
    , I32 <$> anyInt32
    , I64 <$> anyInt64
    , BI  <$> integer (exponentialFrom 0 (-0xffff_ffff) 0xffff_ffff)
    , B8  <$> anyBits8
    , B16 <$> anyBits16
    , B32 <$> anyBits32
    , B64 <$> anyBits64
    , Str <$> string (linear 0 10) printableAscii
    , Ch  <$> printableAscii
    , Db  <$> double (exponentialDoubleFrom 0 (-0xffff_ffff) 0xffff_ffff)
    , PrT <$> primTypes
    , pure WorldVal
    ]

export
precisions : Gen Precision
precisions = element [P 8, P 16, P 32, P 64, Unlimited]

export
intKinds : Gen IntKind
intKinds = choice [Signed <$> precisions, Unsigned <$> element [8,16,32,64]]

export
primFns1 : Gen (PrimFn 1)
primFns1 =
  choice
    [ Neg <$> primTypes
    , [| Cast primTypes primTypes |]
    , element
        [ StrLength
        , StrHead
        , StrTail
        , StrReverse
        , DoubleExp
        , DoubleLog
        , DoubleSin
        , DoubleCos
        , DoubleTan
        , DoubleASin
        , DoubleACos
        , DoubleATan
        , DoubleSqrt
        , DoubleFloor
        , DoubleCeiling
        ]
    ]

export
primFns2 : Gen (PrimFn 2)
primFns2 =
  choice
    [ Add <$> primTypes
    , Sub <$> primTypes
    , Mul <$> primTypes
    , Div <$> primTypes
    , Mod <$> primTypes
    , ShiftL <$> primTypes
    , ShiftR <$> primTypes
    , BAnd <$> primTypes
    , BOr <$> primTypes
    , BXOr <$> primTypes
    , LT <$> primTypes
    , LTE <$> primTypes
    , GT <$> primTypes
    , GTE <$> primTypes
    , EQ <$> primTypes
    , pure StrIndex
    , pure StrCons
    , pure StrAppend
    , pure DoublePow
    , pure Crash
    ]

export
primFns3 : Gen (PrimFn 3)
primFns3 = element [StrSubstr, BelieveMe]
