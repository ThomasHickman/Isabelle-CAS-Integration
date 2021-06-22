structure Tupled_ODE =
struct
local
open Arith_Expr; open Syntax; open HOLogic;

fun Num t n =
  case t of @{typ int} => NInt n | _ => NNat n;
in

fun dest_tupled_lambda (Const (@{const_name case_prod}, _) $ Abs (x, t, e)) =
  let val (xs, e') = dest_tupled_lambda (betapply (Abs (x, t, e), Free (x, t)))
  in (mk_prod (Free (x, t), xs), e') end |
dest_tupled_lambda (Abs (x, t, e)) = (Free (x, t), betapply (Abs (x, t, e), Free (x, t))) |
dest_tupled_lambda e = raise TERM ("dest_tupled_lambda: bad tupled lambda", [e]);

fun term_aexp ivar vs (Const (@{const_name zero_class.zero}, t)) = Num t 0
| term_aexp ivar vs (Const (@{const_name one_class.one}, t)) = Num t 1
| term_aexp ivar vs (c as Const (@{const_name numeral}, t) $ _) = Num t (snd (dest_number c))
| term_aexp ivar vs (Const (n, _) $ e $ f) = BOp (n, term_aexp ivar vs e, term_aexp ivar vs f)
| term_aexp ivar vs (Const (n, _) $ e) = UOp (n, term_aexp ivar vs e)
| term_aexp ivar vs (Free (n, _)) = if (n = ivar) then IVar else if (member (op =) vs n) then SVar n else CVar n
| term_aexp ivar vs (Const (n, _)) = CVar (Long_Name.base_name n);

fun tupled_lam_ode (Abs (ivar, _, t)) =
let 
  val (xs, ode) = dest_tupled_lambda t
  val vs = map Term.term_name (strip_tuple xs)
  val odes = map (term_aexp ivar vs) (strip_tuple ode)
in (vs, {ivar = ivar, odes = Symtab.make (ListPair.zip (vs, odes))})
end |
tupled_lam_ode t = raise TERM ("tupled_lam_ode: incorrect format", [t])

fun aexp_term ivar ctx (NNat n) = HOLogic.mk_number @{typ nat} n
| aexp_term ivar ctx (NInt n) = HOLogic.mk_number @{typ real} n
| aexp_term ivar ctx (UOp (n, e)) = Const (n, dummyT --> dummyT) $ aexp_term ivar ctx e
| aexp_term ivar ctx (BOp (n, e, f)) = Const (n, dummyT --> dummyT --> dummyT) $ aexp_term ivar ctx e $ aexp_term ivar ctx f
| aexp_term ivar ctx (SVar x) = Free (x, @{typ real})
| aexp_term ivar ctx (CVar x) = Free (x, dummyT)
| aexp_term ivar ctx IVar = Free (ivar, @{typ real})

fun sol_tupled_lam ctx ivar vs m 
  = absfree (ivar, @{typ real}) (mk_tuple (map (aexp_term ivar ctx o the o Symtab.lookup m) vs))


(*
fun sol_tupled_lam ctx ivar vs m = Abs (ivar, @{typ real}, Expr_Util.tab_subst ctx (Symtab.map (fn _ => fn e => aexp_sexp ctx e) m))

fun sol_tupled_lam 
*)

end

end