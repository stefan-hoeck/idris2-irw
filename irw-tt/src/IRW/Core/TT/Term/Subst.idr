module IRW.Core.TT.Term.Subst

import IRW.Core.Name.Scoped

import IRW.Core.TT.Binder
import IRW.Core.TT.Subst
import IRW.Core.TT.Term
import IRW.Core.TT.Var

import IRW.Libs.Data.SizeOf

%default total

public export
0 SubstEnv : Type -> Scope -> Scoped
SubstEnv n = Subst (Term n)

substTerm : Substitutable (Term n) (Term n)
substTerms : Substitutable (Term n) (List . Term n)
substBinder : Substitutable (Term n) (Binder . Term n)

substTerm outer dropped env (Local fc r v)
    = find (Local fc r) outer dropped v env
substTerm outer dropped env (Ref fc x name) = Ref fc x name
substTerm outer dropped env (Meta fc n xs)
    = Meta fc n (substTerms outer dropped env xs)
substTerm outer dropped env (Bind fc x b scope)
    = Bind fc x (substBinder outer dropped env b)
                (substTerm (suc outer) dropped env scope)
substTerm outer dropped env (App fc fn arg)
    = App fc (substTerm outer dropped env fn) (substTerm outer dropped env arg)
substTerm outer dropped env (As fc s as pat)
    = As fc s (substTerm outer dropped env as) (substTerm outer dropped env pat)
substTerm outer dropped env (TDelayed fc x y) = TDelayed fc x (substTerm outer dropped env y)
substTerm outer dropped env (TDelay fc x t y)
    = TDelay fc x (substTerm outer dropped env t) (substTerm outer dropped env y)
substTerm outer dropped env (TForce fc r x) = TForce fc r (substTerm outer dropped env x)
substTerm outer dropped env (PrimVal fc c) = PrimVal fc c
substTerm outer dropped env (Erased fc Impossible) = Erased fc Impossible
substTerm outer dropped env (Erased fc Placeholder) = Erased fc Placeholder
substTerm outer dropped env (Erased fc (Dotted t)) = Erased fc (Dotted (substTerm outer dropped env t))
substTerm outer dropped env (TType fc u) = TType fc u

substTerms outer dropped env xs
  = assert_total $ map (substTerm outer dropped env) xs

substBinder outer dropped env b
  = assert_total $ map (substTerm outer dropped env) b

export
substs : SizeOf dropped -> SubstEnv n dropped vs -> Term n (vs++dropped) -> Term n vs
substs dropped env tm = substTerm zero dropped env tm

export
subst : Term n vs -> Term n (Scope.bind vs x) -> Term n vs
subst val tm = substs (suc zero) [<val] tm
