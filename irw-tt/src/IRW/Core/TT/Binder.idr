module IRW.Core.TT.Binder

import Derive.Prelude
import IRW.Algebra
import IRW.Core.FC
import IRW.Core.HasNames

%default total
%language ElabReflection
%hide Language.Reflection.TT.FC
%hide Language.Reflection.TT.Name
%hide Language.Reflection.TT.PiInfo

--------------------------------------------------------------------------------
-- Pi information classifies the kind of pi type this is
--------------------------------------------------------------------------------

public export
data PiInfo t =
  ||| Implicit Pi types (e.g. {0 a : Type} -> ...)
  ||| The argument is to be solved by unification
  Implicit |
  ||| Explicit Pi types (e.g. (x : a) -> ...)
  ||| The argument is to be passed explicitly
  Explicit |
  ||| Auto Pi types (e.g. (fun : Functor f) => ...)
  ||| The argument is to be solved by proof search
  AutoImplicit |
  ||| Default Pi types (e.g. {default True flag : Bool} -> ...)
  ||| The argument is set to the default value if nothing is
  ||| passed explicitly
  DefImplicit t

%runElab derive "PiInfo" [Show]
%name PiInfo pinfo

namespace PiInfo

  export
  isImplicit : PiInfo t -> Bool
  isImplicit Explicit = False
  isImplicit _ = True

||| Heterogeneous equality, provided an heterogeneous equality
||| of default values
export
eqPiInfoBy : (t -> u -> Bool) -> PiInfo t -> PiInfo u -> Bool
eqPiInfoBy eqT = go where

  go : PiInfo t -> PiInfo u -> Bool
  go Implicit Implicit = True
  go Explicit Explicit = True
  go AutoImplicit AutoImplicit = True
  go (DefImplicit t) (DefImplicit t') = eqT t t'
  go _ _ = False

-- There's few places where we need the default - it's just when checking if
-- there's a default during elaboration - so often it's easier just to erase it
-- to a normal implicit
export
forgetDef : PiInfo t -> PiInfo t'
forgetDef Explicit = Explicit
forgetDef Implicit = Implicit
forgetDef AutoImplicit = AutoImplicit
forgetDef (DefImplicit t) = Implicit

export
Interpolation t => Interpolation (PiInfo t) where
  interpolate Implicit = "Implicit"
  interpolate Explicit = "Explicit"
  interpolate AutoImplicit = "AutoImplicit"
  interpolate (DefImplicit t) = "DefImplicit \{t}"

export
Eq t => Eq (PiInfo t) where
  (==) = eqPiInfoBy (==)

export
Foldable1 PiInfo where
  foldl1 f v (DefImplicit x) t = f v x t
  foldl1 f v _ t = v # t

export
Traversable1 PiInfo where
  traverse1 f Implicit t = Implicit # t
  traverse1 f Explicit t = Explicit # t
  traverse1 f AutoImplicit t = AutoImplicit # t
  traverse1 f (DefImplicit x) t = let y # t := f x t in DefImplicit y # t

--------------------------------------------------------------------------------
-- A bound value
--------------------------------------------------------------------------------

||| A bound value along with its `PiInfo`.
||| We cannot use `PiInfo` as metadata for `WithData` because the record is functorial in both
||| `t` and `PiInfo`.
public export
record PiBindData (t : Type) where
  constructor MkPiBindData
  info : PiInfo t
  boundType : t

%runElab derive "PiBindData" [Show]

public export
mapType : (t -> t) -> PiBindData t -> PiBindData t
mapType f = {boundType $= f}

export
Interpolation t => Interpolation (PiBindData t) where
  interpolate (MkPiBindData i t) = "\{i}, \{t}"

export
Foldable1 PiBindData where
  foldl1 f v (MkPiBindData i b) t =
   let v2 # t := Traverse1.foldl1 f v i t in f v2 b t

export
Traversable1 PiBindData where
  traverse1 f (MkPiBindData i b) t =
   let i2 # t := traverse1 f i t
       b2 # t := f b t
    in MkPiBindData i2 b2 # t

--------------------------------------------------------------------------------
-- Different types of binders we may encounter
--------------------------------------------------------------------------------

public export
data Binder : Type -> Type where

     ||| Lambda bound variables with their implicitness
     Lam : FC -> RigCount -> PiInfo t -> (ty : t) -> Binder t

     ||| Let bound variables with their value
     Let : FC -> RigCount -> (val : t) -> (ty : t) -> Binder t

     |||Forall/pi bound variables with their implicitness
     Pi : FC -> RigCount -> PiInfo t -> (ty : t) -> Binder t

     ||| Pattern bound variables. The PiInfo gives the implicitness at the
     ||| point it was bound (Explicit if it was explicitly named in the
     ||| program)
     PVar : FC -> RigCount -> PiInfo t -> (ty : t) -> Binder t

     ||| Variable bound for an as pattern (Like a let, but no computational
     ||| force, and only used on the lhs. Converted to a let on the rhs because
     ||| we want the computational behaviour.)
     PLet : FC -> RigCount -> (val : t) -> (ty : t) -> Binder t

     ||| The type of pattern bound variables
     PVTy : FC -> RigCount -> (ty : t) -> Binder t

%runElab derive "Binder" [Show]

%name Binder bd

export
isLet : Binder t -> Bool
isLet (Let {}) = True
isLet _ = False

export
binderLoc : Binder tm -> FC
binderLoc (Lam fc _ x ty) = fc
binderLoc (Let fc _ val ty) = fc
binderLoc (Pi fc _ x ty) = fc
binderLoc (PVar fc _ p ty) = fc
binderLoc (PLet fc _ val ty) = fc
binderLoc (PVTy fc _ ty) = fc

export
binderType : Binder tm -> tm
binderType (Lam _ _ x ty) = ty
binderType (Let _ _ val ty) = ty
binderType (Pi _ _ x ty) = ty
binderType (PVar _ _ _ ty) = ty
binderType (PLet _ _ val ty) = ty
binderType (PVTy _ _ ty) = ty

export
multiplicity : Binder tm -> RigCount
multiplicity (Lam _ c x ty) = c
multiplicity (Let _ c val ty) = c
multiplicity (Pi _ c x ty) = c
multiplicity (PVar _ c p ty) = c
multiplicity (PLet _ c val ty) = c
multiplicity (PVTy _ c ty) = c

export
piInfo : Binder tm -> PiInfo tm
piInfo (Lam _ c x ty) = x
piInfo (Let _ c val ty) = Explicit
piInfo (Pi _ c x ty) = x
piInfo (PVar _ c p ty) = p
piInfo (PLet _ c val ty) = Explicit
piInfo (PVTy _ c ty) = Explicit

export
isImplicit : Binder tm -> Bool
isImplicit = PiInfo.isImplicit . piInfo

export
setMultiplicity : Binder tm -> RigCount -> Binder tm
setMultiplicity (Lam fc _ x ty) c = Lam fc c x ty
setMultiplicity (Let fc _ val ty) c = Let fc c val ty
setMultiplicity (Pi fc _ x ty) c = Pi fc c x ty
setMultiplicity (PVar fc _ p ty) c = PVar fc c p ty
setMultiplicity (PLet fc _ val ty) c = PLet fc c val ty
setMultiplicity (PVTy fc _ ty) c = PVTy fc c ty

export
Interpolation ty => Interpolation (Binder ty) where
  interpolate (Lam _ c _ t) = "\\\{c} \{t}"
  interpolate (Pi _ c _ t) = "Pi\{c} \{t}"
  interpolate (Let _ c v t) = "let\{c} \{v}:\{t}"
  interpolate (PVar _ c _ t) = "pat\{c} \{t}"
  interpolate (PLet _ c v t) = "plet\{c} \{v}:\{t}"
  interpolate (PVTy _ c t) = "pty\{c} \{t}"

export
setType : Binder tm -> tm -> Binder tm
setType (Lam fc c x _) ty = Lam fc c x ty
setType (Let fc c val _) ty = Let fc c val ty
setType (Pi fc c x _) ty = Pi fc c x ty
setType (PVar fc c p _) ty = PVar fc c p ty
setType (PLet fc c val _) ty = PLet fc c val ty
setType (PVTy fc c _) ty = PVTy fc c ty

export
Functor PiInfo where
  map f p = run1 $ traverse1 (\x,t => f x # t) p

export
Foldable PiInfo where
  foldr f acc p = run1 $ foldr1 (\x,y,t => f x y # t) acc p
  foldl f acc p = run1 $ foldl1 (\x,y,t => f x y # t) acc p
  foldMap f p = run1 $ foldMap1 (\x,t => f x # t) p

export
Functor PiBindData where
  map f (MkPiBindData info type) = MkPiBindData (map f info) (f type)

export
Foldable PiBindData where
  foldr f acc (MkPiBindData info type) = f type (foldr f acc info)
  foldl f acc p = run1 $ foldl1 (\x,y,t => f x y # t) acc p
  foldMap f p = run1 $ foldMap1 (\x,t => f x # t) p

export
Foldable1 Binder where
  foldl1 f v (Lam _ _ p ty) t =
   let v2 # t := Traverse1.foldl1 f v p t in f v2 ty t
  foldl1 f v (Let _ _ p ty) t =
   let v2 # t := f v p t in f v2 ty t
  foldl1 f v (Pi _ _ p ty) t =
   let v2 # t := Traverse1.foldl1 f v p t in f v2 ty t
  foldl1 f v (PVar _ _ p ty) t =
   let v2 # t := Traverse1.foldl1 f v p t in f v2 ty t
  foldl1 f v (PLet _ _ p ty) t =
   let v2 # t := f v p t in f v2 ty t
  foldl1 f v (PVTy _ _ ty) t = f v ty t

export
Traversable1 Binder where
  traverse1 f (Lam fc r p ty) t =
   let p2 # t := Traverse1.traverse1 f p t
       t2 # t :=  f ty t
    in Lam fc r p2 t2 # t
  traverse1 f (Let fc r p ty) t =
   let p2 # t := f p t
       t2 # t := f ty t
    in Let fc r p2 t2 # t
  traverse1 f (Pi fc r p ty) t =
   let p2 # t := Traverse1.traverse1 f p t
       t2 # t :=  f ty t
    in Pi fc r p2 t2 # t
  traverse1 f (PVar fc r p ty) t =
   let p2 # t := Traverse1.traverse1 f p t
       t2 # t :=  f ty t
    in PVar fc r p2 t2 # t
  traverse1 f (PLet fc r p ty) t =
   let p2 # t := f p t
       t2 # t := f ty t
    in PLet fc r p2 t2 # t
  traverse1 f (PVTy fc r ty) t =
   let t2 # t := f ty t
    in PVTy fc r t2 # t

export
Functor Binder where
  map f p = run1 $ traverse1 (\x,t => f x # t) p

export
Foldable Binder where
  foldr f acc p = run1 $ foldr1 (\x,y,t => f x y # t) acc p
  foldl f acc p = run1 $ foldl1 (\x,y,t => f x y # t) acc p
  foldMap f p = run1 $ foldMap1 (\x,t => f x # t) p

export
eqBinderBy : (t -> u -> Bool) -> (Binder t -> Binder u -> Bool)
eqBinderBy eqTU = go where

  go : Binder t -> Binder u -> Bool
  go (Lam _ c p ty) (Lam _ c' p' ty') = c == c' && eqPiInfoBy eqTU p p' && eqTU ty ty'
  go (Let _ c v ty) (Let _ c' v' ty') = c == c' && eqTU v v' && eqTU ty ty'
  go (Pi _ c p ty) (Pi _ c' p' ty')   = c == c' && eqPiInfoBy eqTU p p' && eqTU ty ty'
  go (PVar _ c p ty) (PVar _ c' p' ty') = c == c' && eqPiInfoBy eqTU p p' && eqTU ty ty'
  go (PLet _ c v ty) (PLet _ c' v' ty') = c == c' && eqTU v v' && eqTU ty ty'
  go (PVTy _ c ty) (PVTy _ c' ty') = c == c' && eqTU ty ty'
  go _ _ = False

export
Eq a => Eq (Binder a) where
  (==) = eqBinderBy (==)
