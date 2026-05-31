module IRW.Core.FC

import Data.Maybe
import Derive.Prelude
import Text.Bounds
import IRW.Core.Name.Namespace

%default total
%language ElabReflection
%hide Language.Reflection.TT.FC
%hide Language.Reflection.TT.ModuleIdent
%hide Language.Reflection.TT.OriginDesc
%hide Language.Reflection.TT.VirtualIdent

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

public export
FileName : Type
FileName = String

public export
data VirtualIdent : Type where
  Interactive : VirtualIdent

%runElab derive "VirtualIdent" [Show,Eq]

export
Interpolation VirtualIdent where interpolate _ = "(Interactive)"

public export
data OriginDesc : Type where
  ||| Anything that originates in physical Idris source files is assigned a
  ||| `PhysicalIdrSrc modIdent`,
  |||   where `modIdent` is the top-level module identifier of that file.
  PhysicalIdrSrc : (ident : ModuleIdent) -> OriginDesc
  ||| Anything parsed from a package file is decorated with `PhysicalPkgSrc fname`,
  |||   where `fname` is path to the package file.
  PhysicalPkgSrc : (fname : FileName) -> OriginDesc
  Virtual : (ident : VirtualIdent) -> OriginDesc

%runElab derive "OriginDesc" [Show,Eq]

export
Interpolation OriginDesc where
  interpolate (PhysicalIdrSrc ident) = interpolate ident
  interpolate (PhysicalPkgSrc fname) = fname
  interpolate (Virtual ident)        = interpolate ident

||| A file context is a filename together with starting and ending positions.
||| It's often carried by AST nodes that might have been created from a source
||| file or by the compiler. That makes it useful to have the notion of
||| `EmptyFC` as part of the type.
public export
data FC : Type where
  EmptyFC : FC
  MkFC : OriginDesc -> Position -> Position -> FC

  ||| Virtual FCs are FC attached to desugared/generated code. They can help with marking
  ||| errors, but we shouldn't attach semantic highlighting metadata to them.
  MkVirtualFC : OriginDesc -> Position -> Position -> FC

export
Interpolation FC where
  interpolate EmptyFC             = "EmptyFC"
  interpolate (MkFC i s e)        = "\{i}:\{s}--\{e}"
  interpolate (MkVirtualFC i s e) = "\{i}:\{s}--\{e}"

%runElab derive "FC" [Show,Eq]
%name FC fc

||| A version of a file context that cannot be empty
public export
0 NonEmptyFC : Type
NonEmptyFC = (OriginDesc, Position, Position)

--------------------------------------------------------------------------------
-- Conversion between NonEmptyFC and FC
--------------------------------------------------------------------------------

||| NonEmptyFC always embeds into FC
export
justFC : NonEmptyFC -> FC
justFC (fname, start, end) = MkFC fname start end

||| A view checking whether an arbitrary FC happens to be non-empty
export
isNonEmptyFC : FC -> Maybe NonEmptyFC
isNonEmptyFC (MkFC fn start end) = Just (fn, start, end)
isNonEmptyFC (MkVirtualFC fn start end) = Just (fn, start, end)
isNonEmptyFC EmptyFC = Nothing

||| A view checking whether an arbitrary FC originates from a source location
export
isConcreteFC : FC -> Maybe NonEmptyFC
isConcreteFC (MkFC fn start end) = Just (fn, start, end)
isConcreteFC _ = Nothing

||| Turn an FC into a virtual one
export
virtualiseFC : FC -> FC
virtualiseFC (MkFC fn start end) = MkVirtualFC fn start end
virtualiseFC fc = fc

export
defaultFC : NonEmptyFC
defaultFC = (Virtual Interactive, begin, begin)

export
replFC : FC
replFC = justFC defaultFC

export
toNonEmptyFC : FC -> NonEmptyFC
toNonEmptyFC = fromMaybe defaultFC . isNonEmptyFC

--------------------------------------------------------------------------------
-- Projections
--------------------------------------------------------------------------------

export
origin : NonEmptyFC -> OriginDesc
origin (fn, _, _) = fn

export
startPos : NonEmptyFC -> Position
startPos (_, s, _) = s

export
startLine : NonEmptyFC -> Nat
startLine = line . startPos

export
startCol : NonEmptyFC -> Nat
startCol = col . startPos

export
endPos : NonEmptyFC -> Position
endPos (_, _, e) = e

export
endLine : NonEmptyFC -> Nat
endLine = line . endPos

export
endCol : NonEmptyFC -> Nat
endCol = col . endPos

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

export
boundsToFC : OriginDesc -> Bounds -> FC
boundsToFC o (BS s e) = MkFC o s e
boundsToFC o NoBounds = EmptyFC

export %inline
boundToFC : OriginDesc -> Bounded t -> FC
boundToFC o = boundsToFC o . bounds

export %inline
(.toFC) : (o : OriginDesc) => Bounded t -> FC
x.toFC = boundToFC o x

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

--- Return whether a given file position is within the file context (assuming we're
--- in the right file)
export
within : Position -> NonEmptyFC -> Bool
within p (_, s, e) = p >= s && p <= e

-- Return whether a given line is on the same line as the file context (assuming
-- we're in the right file)
export
onLine : Nat -> NonEmptyFC -> Bool
onLine x (_, s, e) = x >= s.line && x <= e.line

--------------------------------------------------------------------------------
-- Basic operations
--------------------------------------------------------------------------------

export
mergeFC : FC -> FC -> Maybe FC
mergeFC (MkFC n1 s1 e1) (MkFC n2 s2 e2) =
  if n1 == n2 then Just $ MkFC n1 (min s1 s2) (max e1 e2) else Nothing
mergeFC _ _ = Nothing
