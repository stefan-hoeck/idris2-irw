module Gen.TT

import Data.Maybe
import Data.Vect
import public Gen.Name
import public IRW.Algebra
import public IRW.Core.FC
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

-- Only trivial file contexts at the moment
export
fcs : Gen FC
fcs = pure EmptyFC

export
rigCounts : Gen ZeroOneOmega
rigCounts = element [erased,linear,top]

export
vars : (vs : Scope) -> Maybe (Gen $ Var vs)
vars vs =
  case allVars vs <>> [] of
    [] => Nothing
    h::t => Just $ element (h :: fromList t)

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

constGens : Vect 14 (Gen Constant)
constGens =
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
  , PrT <$> primTypes
  , pure WorldVal
  ]

export
constantsNoDb : Gen Constant
constantsNoDb = choice constGens

export
constants : Gen Constant
constants =
  choice $
       (Db <$> double (exponentialDoubleFrom 0 (-0xffff_ffff) 0xffff_ffff))
    :: constGens

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

--------------------------------------------------------------------------------
-- Binders
--------------------------------------------------------------------------------

export
piInfos : Gen a -> Gen (PiInfo a)
piInfos g =
  choice [ DefImplicit <$> g, element [Implicit, Explicit, AutoImplicit]]

export
piBindData : Gen a -> Gen (PiBindData a)
piBindData g = [| MkPiBindData (piInfos g) g |]

export
binders : Gen a -> Gen (Binder a)
binders g =
  choice
    [ [| Lam  fcs rigCounts (piInfos g) g |]
    , [| Let  fcs rigCounts g g |]
    , [| Pi   fcs rigCounts (piInfos g) g |]
    , [| PVar fcs rigCounts (piInfos g) g |]
    , [| PLet fcs rigCounts g g |]
    , [| PVTy fcs rigCounts g |]
    ]

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

export
nameTypes : Gen NameType
nameTypes =
  choice
    [ element [Bound,Func]
    , [| DataCon (bits32 $ linear 0 31) (nat $ linear 0 31) |]
    , [| TyCon (nat $ linear 0 31) |]
    ]

export
lazyReasons : Gen LazyReason
lazyReasons = element [LInf, LLazy, LUnknown]

export
useSides : Gen UseSide
useSides = element [UseLeft, UseRight]

export
whyErased : Gen a -> Gen (WhyErased a)
whyErased g = choice [ Dotted <$> g, element [Placeholder, Impossible]]

terms0 : (vs : Scope) -> Vect 4 (Gen $ Term vs)
terms0 vs =
  [ [| Ref fcs nameTypes names |]
  , [| PrimVal fcs constants |]
  , [| TType fcs names |]
  , maybe
      [| PrimVal fcs constants |]
      (\g => [| Local fcs (maybe bool) g |])
      (vars vs)
  ]

binds : (vs : Scope) -> Nat -> Name -> Gen (Term vs)

termsL : (vs : Scope) -> Nat -> Gen (List $ Term vs)

termsN : (vs : Scope) -> Nat -> Gen (Term vs)
termsN vs 0     = choice (terms0 vs)
termsN vs (S k) =
  choice $
       [| Meta fcs names anyBits32 (termsL vs k) |]
    :: [| App fcs (termsN vs k) (termsN vs k) |]
    :: [| As fcs useSides (termsN vs k) (termsN vs k) |]
    :: [| TDelayed fcs lazyReasons (termsN vs k) |]
    :: [| TDelay fcs lazyReasons (termsN vs k) (termsN vs k) |]
    :: [| TForce fcs lazyReasons (termsN vs k) |]
    :: (names >>= binds vs k)
    :: terms0 vs

termsL vs n = list (linear 0 3) (termsN vs n)

binds vs n v = [| mkBind fcs (binders $ termsN vs n) (termsN (vs:<v) n) |]
  where
    mkBind : FC -> Binder (Term vs) -> Term (vs:<v) -> Term vs
    mkBind fc = Bind fc v

export
terms : (vs : Scope) -> Gen (Term vs)
terms vs = termsN vs 4
