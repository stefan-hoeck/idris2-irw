module IRW.Libs.Data.SnocList.Thin

import IRW.Libs.Data.NatSet

%default total

||| Proof that the elements in the first list also appear
||| in the second list in the same order.
public export
data Thin : SnocList a -> SnocList a -> Type where
  Refl : Thin sx sx
  Drop : Thin sx sy -> Thin sx (sy:<y)
  Keep : Thin sx sy -> Thin (sx:<x) (sy:<x)

export
none : {sx : SnocList a} -> Thin [<] sx
none {sx = [<]} = Refl
none {sx = _ :< _} = Drop none

||| Smart constructor. We should use this to maximise the length
||| of the Refl segment thus getting more short-circuiting behaviours
export
keep : Thin sx sy -> Thin (sx:<x) (sy:<x)
keep Refl = Refl
keep p    = Keep p

export
keeps : (args : SnocList a) -> Thin sx sy -> Thin (sx++args) (sy++args)
keeps [<]     th = th
keeps (sx:<x) th = Keep (keeps sx th)

export
fromNatSet : NatSet -> (sx : SnocList a) -> (sx' ** Thin sx' sx)
fromNatSet ns sx =
  if isEmpty ns then (_ ** Refl) else go 0 sx
  where
    go : Nat -> (sx : SnocList a) -> (sx' ** Thin sx' sx)
    go i [<]     = (_ ** Refl)
    go i (sx:<x) =
     let (sx' ** th) := go (S i) sx
      in if i `elem` ns then (sx' ** Drop th) else (sx':<x ** Keep th)
