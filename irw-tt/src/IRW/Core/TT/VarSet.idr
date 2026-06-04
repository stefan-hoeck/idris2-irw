module IRW.Core.TT.VarSet

import Data.Bits
import IRW.Core.Name.Scoped
import IRW.Core.TT.Var
import IRW.Libs.Data.NatSet
import IRW.Libs.Data.SizeOf

%default total

export
record VarSet (vs : Scope) where
  constructor VS
  vars : NatSet

export %inline
empty : VarSet vs
empty = VS empty

export %inline
elem : Var vs -> VarSet vs -> Bool
elem (MkVar {varIdx} _) = NatSet.elem varIdx . vars

export %inline
isEmpty : VarSet vs -> Bool
isEmpty = NatSet.isEmpty . vars

export %inline
size : VarSet vs -> Nat
size = NatSet.size . vars

export %inline
insert : Var vs -> VarSet vs -> VarSet vs
insert (MkVar {varIdx} _) (VS v) = VS $ NatSet.insert varIdx v

export %inline
delete : Var vs -> VarSet vs -> VarSet vs
delete (MkVar {varIdx} _) (VS v) = VS $ NatSet.delete varIdx v

export %inline
full : SizeOf vs -> VarSet vs
full p = VS $ NatSet.allLessThan p.size

export %inline
intersection : VarSet vs -> VarSet vs -> VarSet vs
intersection (VS x) (VS y) = VS $ NatSet.intersection x y

export %inline
union : VarSet vs -> VarSet vs -> VarSet vs
union (VS x) (VS y) = VS $ NatSet.union x y

export %inline %unsafe
unsafeToList : VarSet vs -> List (Var vs)
unsafeToList (VS x) = believe_me NatSet.toList x

export %inline
toList : {vs : Scope} -> VarSet vs -> List (Var vs)
toList = mapMaybe (`isDeBruijn` vs) . NatSet.toList . vars

||| Pop the zero (whether or not in the set) and shift all the
||| other positions by -1 (useful when coming back from under
||| a binder)
export %inline
dropFirst : VarSet (vs:<v) -> VarSet vs
dropFirst (VS v) = VS $ NatSet.popZ v

export %inline
dropInner : SizeOf inner -> VarSet (vs++inner) -> VarSet vs
dropInner p (VS v) = VS $ NatSet.popNs p.size v

export
FreelyEmbeddable VarSet where

-- TODO: This is new and must be tested
export
GenWeaken VarSet where
  genWeakenNs x y (VS v) = VS $ genWeaken x.size y.size v

export %inline
singleton : Var vs -> VarSet vs
singleton v = insert v empty

export %inline
append : SizeOf inner -> VarSet inner -> VarSet outer -> VarSet (outer++inner)
append p inn out = union (embed inn) (weakenNs p out)

export
fromVarSet : (vs : Scope) -> VarSet vs -> (newvars ** Thin newvars vs)
fromVarSet [<] xs = (Scope.empty ** Refl)
fromVarSet (ns:<n) xs =
    let (_ ** svs) = fromVarSet ns (VarSet.dropFirst xs) in
    if first `VarSet.elem` xs
      then (_ ** Keep svs)
      else (_ ** Drop svs)
