(* Mapping between substitutions and ODEs *)

signature SUBST_ODE =
sig
    val aexp_sexp: Proof.context -> Arith_Expr.AExp -> term
    val sexp_aexp: term -> Arith_Expr.AExp
    val subst_ode: string -> term -> Arith_Expr.SODE
    val ode_subst: Proof.context -> string -> Arith_Expr.AExp Symtab.table -> term
end

structure Subst_ODE : SUBST_ODE =
struct
local
open Arith_Expr;
fun aexp_sexp' ctx (NNat n) = HOLogic.mk_number @{typ nat} n
| aexp_sexp' ctx (NInt n) = HOLogic.mk_number @{typ real} n
| aexp_sexp' ctx (UOp (n, e)) = Const (n, dummyT) $ aexp_sexp' ctx e
| aexp_sexp' ctx (BOp (n, e, f)) = Const (n, dummyT) $ aexp_sexp' ctx e $ aexp_sexp' ctx f
| aexp_sexp' ctx (SVar x) = 
    let val lens = Expr_Util.const_or_free ctx x
    in Const (@{const_name lens_get}, dummyT) $ lens $ Free (Lift_Expr.state_id, dummyT)
    end
| aexp_sexp' ctx (CVar x) = Free (x, dummyT)
| aexp_sexp' ctx IVar = Bound 1 (* 1 because 0 is the state variable *);
in

fun Num t n =
  case t of @{typ int} => NInt n | _ => NNat n;

fun sexp_aexp (Const (@{const_name SEXP}, _) $ Abs (_, _, e)) = sexp_aexp e
| sexp_aexp (Const (@{const_name lens_get}, _) $ n $ _) = SVar (Term.term_name n)
| sexp_aexp (Const (@{const_name zero_class.zero}, t)) = Num t 0
| sexp_aexp (Const (@{const_name one_class.one}, t)) = Num t 1
| sexp_aexp (c as Const (@{const_name numeral}, t) $ _) = Num t (snd (HOLogic.dest_number c))
| sexp_aexp (Const (n, _) $ e $ f) = BOp (n, sexp_aexp e, sexp_aexp f)
| sexp_aexp (Const (n, _) $ e) = UOp (n, sexp_aexp e)
| sexp_aexp (Free (n, _)) = CVar n
| sexp_aexp (Const (n, _)) = CVar (Long_Name.base_name n);

fun aexp_sexp ctx e = Const (@{const_name "SEXP"}, dummyT) $ absfree (Lift_Expr.state_id, dummyT) (aexp_sexp' ctx e);

fun subst_ode ivar s = 
  { ivar = ivar
  , odes = Symtab.make (map (fn (x, e) => (Long_Name.base_name x, sexp_aexp e)) (Symtab.dest (Expr_Util.subst_tab s)))};

fun ode_subst ctx ivar m = Abs (ivar, @{typ real}, Expr_Util.tab_subst ctx (Symtab.map (fn _ => fn e => aexp_sexp ctx e) m));

end

end