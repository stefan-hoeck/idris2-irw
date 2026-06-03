module IRW.Core.TT.Subst

import IRW.Core.Name.Scoped
import IRW.Core.TT.Var

import IRW.Libs.Data.SizeOf

%default total

public export
data Subst : Scoped -> Scope -> Scoped where
  Lin : Subst tm [<] vars
  (:<) : Subst tm ds vars -> tm vars -> Subst tm (ds:<d) vars

public export
empty : Subst tm [<] vars
empty = [<]

namespace Var

  export
  index : Subst tm ds vars -> Var ds -> tm vars
  index [<] (MkVar p) impossible
  index (_ :< t)  (MkVar First) = t
  index (ts :< _) (MkVar (Later p)) = index ts (MkVar p)

export
findDrop :
     (Var vars -> tm vars)
  -> SizeOf dropped
  -> Var (vars++dropped)
  -> Subst tm dropped vars
  -> tm vars
findDrop k s var sub =
  case locateVar s var of
    Left var => index sub var
    Right var => k var

export
find :
     {auto wk : GenWeaken tm}
  -> (forall vars. Var vars -> tm vars)
  -> SizeOf outer
  -> SizeOf dropped
  -> Var ((vars ++ dropped) ++ outer)
  -> Subst tm dropped vars
  -> tm (vars++outer)
find k outer dropped var sub =
  case locateVar outer var of
    Left var => k (embed var)
    Right var => weakenNs outer (findDrop k dropped var sub)

public export
0 Substitutable : Scoped -> Scoped -> Type
Substitutable val tm =
     {0 outer, dropped, vars : Scope}
  -> SizeOf outer
  -> SizeOf dropped
  -> Subst val dropped vars
  -> tm ((vars ++ dropped) ++ outer)
  -> tm (vars ++ outer)
