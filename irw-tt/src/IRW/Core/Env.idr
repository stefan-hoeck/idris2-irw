module IRW.Core.Env

import Data.List
import Decidable.HDecEq
import IRW.Core.TT
import IRW.Libs.Data.SizeOf

%default total

||| Environment containing types and values of local variables
public export
data Env : (tm : Scoped) -> Scope -> Type where
  Lin : Env tm Scope.empty
  (:<) : Env tm vs -> Binder (tm vs) -> Env tm (vs:<x)

%name Env rho

public export
empty : Env tm Scope.empty
empty = [<]

export
extend : (x : Name) -> Env tm vs -> Binder (tm vs) -> Env tm (vs:<x)
extend x = (:<) {x}

export
(++) : {ns : _} -> Env Term ns -> Env Term vs -> Env Term (ns ++ vs)
(++) e (bs:<b) = (e++bs) :< map embed b
(++) e [<]     = e

export
length : Env tm xs -> Nat
length [<]     = 0
length (xs:<_) = S (length xs)

export
lengthNoLet : Env tm xs -> Nat
lengthNoLet [<]          = 0
lengthNoLet (xs:<Let {}) = lengthNoLet xs
lengthNoLet (xs:<_)      = S (lengthNoLet xs)

export
lengthExplicitPi : Env tm xs -> Nat
lengthExplicitPi [<]                        = 0
lengthExplicitPi (rho :< Pi _ _ Explicit _) = S (lengthExplicitPi rho)
lengthExplicitPi (rho :< _)                 = lengthExplicitPi rho

export
namesNoLet : {xs : _} -> Env tm xs -> SnocList Name
namesNoLet [<] = [<]
namesNoLet (xs :< Let {}) = namesNoLet xs
namesNoLet {xs = _ :< x} (env:<_) = namesNoLet env :< x

export
eraseLinear : Env tm vs -> Env tm vs
eraseLinear [<] = Env.empty
eraseLinear (bs:<b) =
  if isLinear (multiplicity b)
     then eraseLinear bs :< setMultiplicity b erased
     else eraseLinear bs :< b

export
getErased : {0 vs : _} -> Env tm vs -> SnocList (Var vs)
getErased env = go env zero
  where
    go : Env tm xs -> LSizeOf seen -> SnocList (Var (xs <>< seen))
    go [<]     p = [<]
    go (bs:<b) p =
      if isErased (multiplicity b)
         then go bs (suc p) :< mkVarFishly p
         else go bs (suc p)

public export
data IsDefined : Name -> Scope -> Type where
  IsDef : {idx : _} -> RigCount -> (0 p : IsVar n idx vs) -> IsDefined n vs

export
defined :
     {vars : _}
  -> (n : Name)
  -> Env Term vars
  -> Maybe0 (IsDefined n vars)
defined n [<] = Nothing0
defined {vars = xs:<x} n (env:<b) =
  case hdecEq n x of
    Nothing0 => map(\(IsDef r p) => IsDef r (Later p)) (defined n env)
    Just0 p  => Just0 $ rewrite p in IsDef (multiplicity b) First

||| Bind additional pattern variables in an LHS, when checking an LHS in an
||| outer environment
export
bindEnv : {vs : _} -> FC -> Env Term vs -> (tm : Term vs) -> ClosedTerm
bindEnv loc [<]      tm = tm
bindEnv loc (env:<b) tm =
  bindEnv loc env $
    Bind loc _ (PVar (binderLoc b) (multiplicity b) Explicit (binderType b)) tm

-- Weaken by all the names at once at the end, to save multiple traversals
-- in big environments
-- Also reversing the names at the end saves significant time over concatenating
-- when environments get fairly big.
getBinderUnder :
     {auto gw : GenWeaken tm}
  -> {vars : _}
  -> {idx : Nat}
  -> (ns : Scope)
  -> (0 p : IsVar x idx vars)
  -> Env tm vars
  -> Binder (tm (reverseOnto ns vars))
getBinderUnder {idx = Z} {vars = vs:<v} ns First (env:<b) =
  let res := map (weakenNs (reverse (mkSizeOf (ns:<v)))) b
   in ?fooo
  -- rewrite revOnto vs (ns:<v)
  -- in map (weakenNs (reverse (mkSizeOf (ns:<v)))) b
getBinderUnder {idx = S k} {vars = vs:<v} ns (Later lp) (env:<b) =
  getBinderUnder (ns:<v) lp env

-- export
-- getBinder : Weaken tm =>
--             {vars : _} -> {idx : Nat} ->
--             (0 p : IsVar x idx vars) -> Env tm vars -> Binder (tm vars)
-- getBinder el env = getBinderUnder Scope.empty el env
--
-- -- For getBinderLoc, we are not reusing getBinder because there is no need to
-- -- needlessly weaken stuff;
-- export
-- getBinderLoc : {vars : _} -> {idx : Nat} -> (0 p : IsVar x idx vars) -> Env tm vars -> FC
-- getBinderLoc {idx = Z}   First     (b :: _)   = binderLoc b
-- getBinderLoc {idx = S k} (Later p) (_ :: env) = getBinderLoc p env
--
-- -- Make a type which abstracts over an environment
-- -- Don't include 'let' bindings, since they have a concrete value and
-- -- shouldn't be generalised
-- export
-- abstractEnvType : {vars : _} ->
--                   FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
-- abstractEnvType fc [] tm = tm
-- abstractEnvType fc (Let fc' c val ty :: env) tm
--     = abstractEnvType fc env (Bind fc _ (Let fc' c val ty) tm)
-- abstractEnvType fc (Pi fc' c e ty :: env) tm
--     = abstractEnvType fc env (Bind fc _ (Pi fc' c e ty) tm)
-- abstractEnvType fc (b :: env) tm
--     = let bnd = Pi (binderLoc b) (multiplicity b) Explicit (binderType b)
--        in abstractEnvType fc env (Bind fc _ bnd tm)
--
-- -- As above, for the corresponding term
-- export
-- abstractEnv : {vars : _} ->
--               FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
-- abstractEnv fc [] tm = tm
-- abstractEnv fc (Let fc' c val ty :: env) tm
--     = abstractEnv fc env (Bind fc _ (Let fc' c val ty) tm)
-- abstractEnv fc (b :: env) tm
--     = let bnd = Lam (binderLoc b) (multiplicity b) Explicit (binderType b)
--       in abstractEnv fc env (Bind fc _ bnd tm)
--
-- -- As above, but abstract over all binders including lets
-- export
-- abstractFullEnvType : {vars : _} ->
--                       FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
-- abstractFullEnvType fc [] tm = tm
-- abstractFullEnvType fc (Pi fc' c e ty :: env) tm
--     = abstractFullEnvType fc env (Bind fc _ (Pi fc' c e ty) tm)
-- abstractFullEnvType fc (b :: env) tm
--     = let bnd = Pi fc (multiplicity b) Explicit (binderType b)
--       in abstractFullEnvType fc env (Bind fc _ bnd tm)
--
-- export
-- mkExplicit : Env Term vs -> Env Term vs
-- mkExplicit [] = Env.empty
-- mkExplicit (Pi fc c _ ty :: env) = Pi fc c Explicit ty :: mkExplicit env
-- mkExplicit (b :: env) = b :: mkExplicit env
--
-- export
-- letToLam : Env Term vars -> Env Term vars
-- letToLam [] = []
-- letToLam (Let fc c val ty :: env) = Lam fc c Explicit ty :: letToLam env
-- letToLam (b :: env) = b :: letToLam env
--
-- mutual
--   findUsed : {vars : _} ->
--              Env Term vars -> VarSet vars -> Term vars -> VarSet vars
--   findUsed env used (Local fc r idx p)
--       = let v := MkVar p in
--         if v `elem` used
--            then used
--            else assert_total (findUsedInBinder env (VarSet.insert v used)
--                                                (getBinder p env))
--   findUsed env used (Meta _ _ _ args)
--       = findUsedArgs env used args
--     where
--       findUsedArgs : Env Term vars -> VarSet vars -> List (Term vars) -> VarSet vars
--       findUsedArgs env u [] = u
--       findUsedArgs env u (a :: as)
--           = findUsedArgs env (findUsed env u a) as
--   findUsed env used (Bind fc x b tm)
--       = assert_total $
--           VarSet.dropFirst (findUsed (b :: env)
--                           (weaken {tm = VarSet} (findUsedInBinder env used b))
--                           tm)
--   findUsed env used (App fc fn arg)
--       = findUsed env (findUsed env used fn) arg
--   findUsed env used (As fc s a p)
--       = findUsed env (findUsed env used a) p
--   findUsed env used (TDelayed fc r tm)
--       = findUsed env used tm
--   findUsed env used (TDelay fc r ty tm)
--       = findUsed env (findUsed env used ty) tm
--   findUsed env used (TForce fc r tm)
--       = findUsed env used tm
--   findUsed env used (Erased fc (Dotted tm))
--       = findUsed env used tm
--   findUsed env used _ = used
--
--   findUsedInBinder : {vars : _} ->
--                      Env Term vars -> VarSet vars ->
--                      Binder (Term vars) -> VarSet vars
--   findUsedInBinder env used (Let _ _ val ty)
--     = findUsed env (findUsed env used val) ty
--   findUsedInBinder env used (PLet _ _ val ty)
--     = findUsed env (findUsed env used val) ty
--   findUsedInBinder env used b = findUsed env used (binderType b)
--
-- export
-- findUsedLocs : {vars : _} ->
--                Env Term vars -> Term vars -> VarSet vars
-- findUsedLocs env tm = findUsed env VarSet.empty tm
--
-- mkShrinkSub : {n : _} ->
--               (vars : _) -> VarSet (n :: vars) ->
--               (newvars ** Thin newvars (n :: vars))
-- mkShrinkSub [] els
--     = if first `VarSet.elem` els
--          then (_ ** Keep Refl)
--          else (_ ** Drop Refl)
-- mkShrinkSub (x :: xs) els
--     = let (_ ** subRest) = mkShrinkSub xs (VarSet.dropFirst els) in
--       if first `VarSet.elem` els
--         then (_ ** Keep subRest)
--         else (_ ** Drop subRest)
--
-- mkShrink : {vars : _} ->
--            VarSet vars ->
--            (newvars ** Thin newvars vars)
-- mkShrink {vars = []} xs = (_ ** Refl)
-- mkShrink {vars = v :: vs} xs = mkShrinkSub _ xs
--
-- -- Find the smallest subset of the environment which is needed to type check
-- -- the given term
-- export
-- findSubEnv : {vars : _} ->
--              Env Term vars -> Term vars ->
--              (vars' : Scope ** Thin vars' vars)
-- findSubEnv env tm = mkShrink (findUsedLocs env tm)
--
-- export
-- shrinkEnv : Env Term vars -> Thin newvars vars -> Maybe (Env Term newvars)
-- shrinkEnv env Refl = Just env
-- shrinkEnv (b :: env) (Drop p) = shrinkEnv env p
-- shrinkEnv (b :: env) (Keep p)
--     = do env' <- shrinkEnv env p
--          b' <- assert_total (shrinkBinder b p)
--          pure (b' :: env')
--
-- export
-- mkEnvOnto : FC -> (xs : List Name) -> Env Term ys -> Env Term (xs ++ ys)
-- mkEnvOnto fc [] vs = vs
-- mkEnvOnto fc (n :: ns) vs
--    = PVar fc top Explicit (Erased fc Placeholder)
--    :: mkEnvOnto fc ns vs
--
-- -- Make a dummy environment, if we genuinely don't care about the values
-- -- and types of the contents.
-- -- We use this when building and comparing case trees.
-- export
-- mkEnv : FC -> (vs : Scope) -> Env Term vs
-- mkEnv fc [] = []
-- mkEnv fc (n :: ns) = PVar fc top Explicit (Erased fc Placeholder) :: mkEnv fc ns
--
-- -- Update an environment so that all names are guaranteed unique. In the
-- -- case of a clash, the most recently bound is left unchanged.
-- --
-- -- TODO replace list of `used` names with a proper set
-- export
-- uniqifyEnv : {vars : _} ->
--              Env Term vars ->
--              (vars' ** (Env Term vars', CompatibleVars vars vars'))
-- uniqifyEnv env = uenv [] env
--   where
--     next : Name -> Name
--     next (MN n i) = MN n (i + 1)
--     next (UN n) = MN (displayUserName n) 0
--     next (NS ns n) = NS ns (next n)
--     next n = MN (show n) 0
--
--     uniqueLocal : List Name -> Name -> Name
--     uniqueLocal vs n
--        = if n `elem` vs
--                  -- we'll find a new name eventualy since the list of names
--                  -- is empty, and next generates something new. But next has
--                  -- to be correct... an exercise for someone: this could
--                  -- probebly be done without an assertion by making a stream of
--                  -- possible names...
--             then assert_total (uniqueLocal vs (next n))
--             else n
--
--     uenv : {vars : _} ->
--            List Name -> Env Term vars ->
--            (vars' ** (Env Term vars', CompatibleVars vars vars'))
--     uenv used [] = ([] ** ([], Pre))
--     uenv used {vars = v :: vs} (b :: bs)
--         = if v `elem` used
--              then let v' = uniqueLocal used v
--                       (vs' ** (env', compat)) = uenv (v' :: used) bs
--                       b' = map (compatNs compat) b in
--                   (v' :: vs' ** (b' :: env', Ext compat))
--              else let (vs' ** (env', compat)) = uenv (v :: used) bs
--                       b' = map (compatNs compat) b in
--                   (v :: vs' ** (b' :: env', Ext compat))
--
-- export
-- allVars : {0 vars : _} -> Env Term vars -> List (Var vars)
-- allVars env = go env [<] where
--
--   go :  {0 vars : _} -> Env Term vars ->
--         {0 seen : SnocList Name} -> SizeOf seen ->
--         List (Var (seen <>> vars))
--   go [] _ = []
--   go (v :: vs) p = mkVarChiply p :: go vs (p :< _)
--
--
-- export
-- allVarsNoLet : {0 vars : _} -> Env Term vars -> List (Var vars)
-- allVarsNoLet env = go env [<] where
--
--   go :  {0 vars : _} -> Env Term vars ->
--         {0 seen : SnocList Name} -> SizeOf seen ->
--         List (Var (seen <>> vars))
--   go [] _ = []
--   go (Let _ _ _ _ :: vs) p = go vs (p :< _)
--   go (v :: vs) p = mkVarChiply p :: go vs (p :< _)
--
-- export
-- close : FC -> String -> Env Term vars -> Term vars -> ClosedTerm
-- close fc nm env tm
--   = let (s, env) = mkSubstEnv 0 env in
--     substs s env (rewrite appendNilRightNeutral vars in tm)
--
--   where
--     mkSubstEnv : Int -> Env Term vs -> (SizeOf vs, SubstEnv vs Scope.empty)
--     mkSubstEnv i [] = (zero, Subst.empty)
--     mkSubstEnv i (v :: vs)
--        = let (s, env) = mkSubstEnv (i + 1) vs in
--          (suc s, Ref fc Bound (MN nm i) :: env)
