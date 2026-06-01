module IRW.Core.TT.Primitive

import Data.Maybe0 as M0
import Data.String
import Data.Vect
import Derive.HDecEq
import Derive.Prelude
import IRW.Core.Name
import IRW.Libs.Data.Ordering.Extra

%default total
%hide Language.Reflection.TT.Constant
%hide Language.Reflection.TT.Name
%hide Language.Reflection.TT.PrimType
%language ElabReflection

public export
data PrimType
    = IntType
    | Int8Type
    | Int16Type
    | Int32Type
    | Int64Type
    | IntegerType
    | Bits8Type
    | Bits16Type
    | Bits32Type
    | Bits64Type
    | StringType
    | CharType
    | DoubleType
    | WorldType

%runElab derive "PrimType" [Show,Eq,Ord,HDecEq]
%name PrimType pty

export
Interpolation PrimType where
  interpolate IntType = "Int"
  interpolate Int8Type = "Int8"
  interpolate Int16Type = "Int16"
  interpolate Int32Type = "Int32"
  interpolate Int64Type = "Int64"
  interpolate IntegerType = "Integer"
  interpolate Bits8Type = "Bits8"
  interpolate Bits16Type = "Bits16"
  interpolate Bits32Type = "Bits32"
  interpolate Bits64Type = "Bits64"
  interpolate StringType = "String"
  interpolate CharType = "Char"
  interpolate DoubleType = "Double"
  interpolate WorldType = "%World"

public export
data Constant
    = I   Int
    | I8  Int8
    | I16 Int16
    | I32 Int32
    | I64 Int64
    | BI  Integer
    | B8  Bits8
    | B16 Bits16
    | B32 Bits32
    | B64 Bits64
    | Str String
    | Ch  Char
    | Db  Double
    | PrT PrimType
    | WorldVal

%runElab derive "Constant" [Show,Eq,Ord]
%name Constant cst

||| Return the primitive type of a constant.
||| For PrT, return Nothing.
export
primType : Constant -> Maybe PrimType
primType (I {})   = Just IntType
primType (I8 {})  = Just Int8Type
primType (I16 {}) = Just Int16Type
primType (I32 {}) = Just Int32Type
primType (I64 {}) = Just Int64Type
primType (BI {})  = Just IntegerType
primType (B8 {})  = Just Bits8Type
primType (B16 {}) = Just Bits16Type
primType (B32 {}) = Just Bits32Type
primType (B64 {}) = Just Bits64Type
primType (Str {}) = Just StringType
primType (Ch {})  = Just CharType
primType (Db {})  = Just DoubleType
primType (PrT {}) = Nothing
primType WorldVal = Just WorldType

export
isConstantType : Name -> Maybe PrimType
isConstantType (UN (Basic n)) = case n of
  "Int"     => Just IntType
  "Int8"    => Just Int8Type
  "Int16"   => Just Int16Type
  "Int32"   => Just Int32Type
  "Int64"   => Just Int64Type
  "Integer" => Just IntegerType
  "Bits8"   => Just Bits8Type
  "Bits16"  => Just Bits16Type
  "Bits32"  => Just Bits32Type
  "Bits64"  => Just Bits64Type
  "String"  => Just StringType
  "Char"    => Just CharType
  "Double"  => Just DoubleType
  "%World"  => Just WorldType
  _ => Nothing
isConstantType _ = Nothing

export
isPrimType : Constant -> Bool
isPrimType (PrT _) = True
isPrimType _       = False

export
HDecEq Constant where
  hdecEq (I x) (I y)       = M0.maybeCong I (hdecEq x y)
  hdecEq (I8 x) (I8 y)     = M0.maybeCong I8 (hdecEq x y)
  hdecEq (I16 x) (I16 y)   = M0.maybeCong I16 (hdecEq x y)
  hdecEq (I32 x) (I32 y)   = M0.maybeCong I32 (hdecEq x y)
  hdecEq (I64 x) (I64 y)   = M0.maybeCong I64 (hdecEq x y)
  hdecEq (B8 x) (B8 y)     = M0.maybeCong B8 (hdecEq x y)
  hdecEq (B16 x) (B16 y)   = M0.maybeCong B16 (hdecEq x y)
  hdecEq (B32 x) (B32 y)   = M0.maybeCong B32 (hdecEq x y)
  hdecEq (B64 x) (B64 y)   = M0.maybeCong B64 (hdecEq x y)
  hdecEq (BI x) (BI y)     = M0.maybeCong BI (hdecEq x y)
  hdecEq (Str x) (Str y)   = M0.maybeCong Str (hdecEq x y)
  hdecEq (Ch x) (Ch y)     = M0.maybeCong Ch (hdecEq x y)
  hdecEq (Db x) (Db y)     = Nothing0 -- no DecEq for Doubles!
  hdecEq (PrT x) (PrT y)   = M0.maybeCong PrT (hdecEq x y)
  hdecEq WorldVal WorldVal = Just0 Refl
  hdecEq _        _        = Nothing0

export
Interpolation Constant where
  interpolate (I x) = show x
  interpolate (I8 x) = show x
  interpolate (I16 x) = show x
  interpolate (I32 x) = show x
  interpolate (I64 x) = show x
  interpolate (BI x) = show x
  interpolate (B8 x) = show x
  interpolate (B16 x) = show x
  interpolate (B32 x) = show x
  interpolate (B64 x) = show x
  interpolate (Str x) = show x
  interpolate (Ch x) = show x
  interpolate (Db x) = show x
  interpolate (PrT x) = interpolate x
  interpolate WorldVal = "%MkWorld"

||| for typecase
export %inline
primTypeTag : PrimType -> Nat
-- 1 = ->, 2 = Type
primTypeTag t = 3 + cast (conIndexPrimType t)

||| Precision of integral types.
public export
data Precision = P Nat | Unlimited

%runElab derive "Precision" [Show,Eq,Ord]
%name Precision prec

||| so far, we only support limited precision
||| unsigned integers
public export
data IntKind = Signed Precision | Unsigned Nat

%runElab derive "IntKind" [Show,Eq]

public export
intKind : PrimType -> Maybe IntKind
intKind IntegerType = Just $ Signed Unlimited
intKind Int8Type    = Just . Signed   $ P 8
intKind Int16Type   = Just . Signed   $ P 16
intKind Int32Type   = Just . Signed   $ P 32
intKind Int64Type   = Just . Signed   $ P 64
intKind IntType     = Just . Signed   $ P 64
intKind Bits8Type   = Just $ Unsigned 8
intKind Bits16Type  = Just $ Unsigned 16
intKind Bits32Type  = Just $ Unsigned 32
intKind Bits64Type  = Just $ Unsigned 64
intKind _           = Nothing

public export
precision : IntKind -> Precision
precision (Signed p)   = p
precision (Unsigned p) = P p

-- All the internal operators, parameterised by their arity
public export
data PrimFn : Nat -> Type where
     Add : (ty : PrimType) -> PrimFn 2
     Sub : (ty : PrimType) -> PrimFn 2
     Mul : (ty : PrimType) -> PrimFn 2
     Div : (ty : PrimType) -> PrimFn 2
     Mod : (ty : PrimType) -> PrimFn 2
     Neg : (ty : PrimType) -> PrimFn 1
     ShiftL : (ty : PrimType) -> PrimFn 2
     ShiftR : (ty : PrimType) -> PrimFn 2

     BAnd : (ty : PrimType) -> PrimFn 2
     BOr : (ty : PrimType) -> PrimFn 2
     BXOr : (ty : PrimType) -> PrimFn 2

     LT  : (ty : PrimType) -> PrimFn 2
     LTE : (ty : PrimType) -> PrimFn 2
     EQ  : (ty : PrimType) -> PrimFn 2
     GTE : (ty : PrimType) -> PrimFn 2
     GT  : (ty : PrimType) -> PrimFn 2

     StrLength : PrimFn 1
     StrHead : PrimFn 1
     StrTail : PrimFn 1
     StrIndex : PrimFn 2
     StrCons : PrimFn 2
     StrAppend : PrimFn 2
     StrReverse : PrimFn 1
     StrSubstr : PrimFn 3

     DoubleExp : PrimFn 1
     DoubleLog : PrimFn 1
     DoublePow : PrimFn 2
     DoubleSin : PrimFn 1
     DoubleCos : PrimFn 1
     DoubleTan : PrimFn 1
     DoubleASin : PrimFn 1
     DoubleACos : PrimFn 1
     DoubleATan : PrimFn 1
     DoubleSqrt : PrimFn 1
     DoubleFloor : PrimFn 1
     DoubleCeiling : PrimFn 1

     Cast : PrimType -> PrimType -> PrimFn 1
     BelieveMe : PrimFn 3
     Crash : PrimFn 2

%runElab deriveIndexed "PrimFn" [Show,ConIndex]
%name PrimFn f

export
Interpolation (PrimFn arity) where
  interpolate (Add ty) = "+" ++ interpolate ty
  interpolate (Sub ty) = "-" ++ interpolate ty
  interpolate (Mul ty) = "*" ++ interpolate ty
  interpolate (Div ty) = "/" ++ interpolate ty
  interpolate (Mod ty) = "%" ++ interpolate ty
  interpolate (Neg ty) = "neg " ++ interpolate ty
  interpolate (ShiftL ty) = "shl " ++ interpolate ty
  interpolate (ShiftR ty) = "shr " ++ interpolate ty
  interpolate (BAnd ty) = "and " ++ interpolate ty
  interpolate (BOr ty) = "or " ++ interpolate ty
  interpolate (BXOr ty) = "xor " ++ interpolate ty
  interpolate (LT ty) = "<" ++ interpolate ty
  interpolate (LTE ty) = "<=" ++ interpolate ty
  interpolate (EQ ty) = "==" ++ interpolate ty
  interpolate (GTE ty) = ">=" ++ interpolate ty
  interpolate (GT ty) = ">" ++ interpolate ty
  interpolate StrLength = "op_strlen"
  interpolate StrHead = "op_strhead"
  interpolate StrTail = "op_strtail"
  interpolate StrIndex = "op_strindex"
  interpolate StrCons = "op_strcons"
  interpolate StrAppend = "++"
  interpolate StrReverse = "op_strrev"
  interpolate StrSubstr = "op_strsubstr"
  interpolate DoubleExp = "op_doubleExp"
  interpolate DoubleLog = "op_doubleLog"
  interpolate DoublePow = "op_doublePow"
  interpolate DoubleSin = "op_doubleSin"
  interpolate DoubleCos = "op_doubleCos"
  interpolate DoubleTan = "op_doubleTan"
  interpolate DoubleASin = "op_doubleASin"
  interpolate DoubleACos = "op_doubleACos"
  interpolate DoubleATan = "op_doubleATan"
  interpolate DoubleSqrt = "op_doubleSqrt"
  interpolate DoubleFloor = "op_doubleFloor"
  interpolate DoubleCeiling = "op_doubleCeiling"
  interpolate (Cast x y) = "cast-" ++ interpolate x ++ "-" ++ interpolate y
  interpolate BelieveMe = "believe_me"
  interpolate Crash = "crash"

export
[Sugared] Show (PrimFn arity) where
  show (Add ty) = "+"
  show (Sub ty) = "-"
  show (Mul ty) = "*"
  show (Div ty) = "div"
  show (Mod ty) = "mod"
  show (Neg ty) = "-"
  show (ShiftL ty) = "shiftl"
  show (ShiftR ty) = "shiftr"
  show (BAnd ty) = "&&"
  show (BOr ty) = "||"
  show (BXOr ty) = "xor"
  show (LT ty) = "<"
  show (LTE ty) = "<="
  show (EQ ty) = "=="
  show (GTE ty) = ">="
  show (GT ty) = ">"
  show StrLength = "length"
  show StrHead = "head"
  show StrTail = "tail"
  show StrIndex = "op_strindex"
  show StrCons = "::"
  show StrAppend = "++"
  show StrReverse = "reverse"
  show StrSubstr = "op_strsubstr"
  show DoubleExp = "exp"
  show DoubleLog = "log"
  show DoublePow = "pow"
  show DoubleSin = "sin"
  show DoubleCos = "cos"
  show DoubleTan = "tan"
  show DoubleASin = "asin"
  show DoubleACos = "acos"
  show DoubleATan = "atan"
  show DoubleSqrt = "sqrt"
  show DoubleFloor = "floor"
  show DoubleCeiling = "ceiling"
  show (Cast x y) = "cast-\{x}-\{y}"
  show BelieveMe = "believe_me"
  show Crash = "crash"

export
primFnEq : PrimFn a1 -> PrimFn a2 -> Maybe0 (a1 = a2)
primFnEq (Add t1) (Add t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (Sub t1) (Sub t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (Mul t1) (Mul t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (Div t1) (Div t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (Mod t1) (Mod t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (Neg t1) (Neg t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (ShiftL t1) (ShiftL t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (ShiftR t1) (ShiftR t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (BAnd t1) (BAnd t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (BOr t1) (BOr t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (BXOr t1) (BXOr t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (LT t1) (LT t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (LTE t1) (LTE t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (EQ t1) (EQ t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (GTE t1) (GTE t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq (GT t1) (GT t2) = if t1 == t2 then Just0 Refl else Nothing0
primFnEq StrLength StrLength = Just0 Refl
primFnEq StrHead StrHead = Just0 Refl
primFnEq StrTail StrTail = Just0 Refl
primFnEq StrIndex StrIndex = Just0 Refl
primFnEq StrCons StrCons = Just0 Refl
primFnEq StrAppend StrAppend = Just0 Refl
primFnEq StrReverse StrReverse = Just0 Refl
primFnEq StrSubstr StrSubstr = Just0 Refl
primFnEq DoubleExp DoubleExp = Just0 Refl
primFnEq DoubleLog DoubleLog = Just0 Refl
primFnEq DoublePow DoublePow = Just0 Refl
primFnEq DoubleSin DoubleSin = Just0 Refl
primFnEq DoubleCos DoubleCos = Just0 Refl
primFnEq DoubleTan DoubleTan = Just0 Refl
primFnEq DoubleASin DoubleASin = Just0 Refl
primFnEq DoubleACos DoubleACos = Just0 Refl
primFnEq DoubleATan DoubleATan = Just0 Refl
primFnEq DoubleSqrt DoubleSqrt = Just0 Refl
primFnEq DoubleFloor DoubleFloor = Just0 Refl
primFnEq DoubleCeiling DoubleCeiling = Just0 Refl
primFnEq (Cast f1 t1) (Cast f2 t2) = if f1 == f2 && t1 == t2 then Just0 Refl else Nothing0
primFnEq BelieveMe BelieveMe = Just0 Refl
primFnEq Crash Crash = Just0 Refl
primFnEq _ _ = Nothing0

export
primFnCmp : PrimFn a1 -> PrimFn a2 -> Ordering
primFnCmp (Add t1) (Add t2) = compare t1 t2
primFnCmp (Sub t1) (Sub t2) = compare t1 t2
primFnCmp (Mul t1) (Mul t2) = compare t1 t2
primFnCmp (Div t1) (Div t2) = compare t1 t2
primFnCmp (Mod t1) (Mod t2) = compare t1 t2
primFnCmp (Neg t1) (Neg t2) = compare t1 t2
primFnCmp (ShiftL t1) (ShiftL t2) = compare t1 t2
primFnCmp (ShiftR t1) (ShiftR t2) = compare t1 t2
primFnCmp (BAnd t1) (BAnd t2) = compare t1 t2
primFnCmp (BOr t1) (BOr t2) = compare t1 t2
primFnCmp (BXOr t1) (BXOr t2) = compare t1 t2
primFnCmp (LT t1) (LT t2) = compare t1 t2
primFnCmp (LTE t1) (LTE t2) = compare t1 t2
primFnCmp (EQ t1) (EQ t2) = compare t1 t2
primFnCmp (GTE t1) (GTE t2) = compare t1 t2
primFnCmp (GT t1) (GT t2) = compare t1 t2
primFnCmp (Cast f1 t1) (Cast f2 t2) = compare f1 f2 `thenCmp` compare t1 t2
primFnCmp f1 f2 = compare (conIndexPrimFn f1) (conIndexPrimFn f2)
