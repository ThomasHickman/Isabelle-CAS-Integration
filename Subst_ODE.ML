(* Mapping between substitutions and ODEs *)

signature SUBST_ODE =
sig
    val aexp_sexp: Proof.context -> Arith_Expr.AExp -> term
    val sexp_aexp: term -> Arith_Expr.AExp
    val subst_ode: string -> term -> Arith_Expr.SODE
end

structure Subst_ODE : SUBST_ODE =
struct
local
open Arith_Expr;
fun aexp_sexp' ctx (Num n) = HOLogic.mk_number @{typ real} n
| aexp_sexp' ctx (UOp (n, e)) = Const (n, dummyT) $ aexp_sexp' ctx e
| aexp_sexp' ctx (BOp (n, e, f)) = Const (n, dummyT) $ aexp_sexp' ctx e $ aexp_sexp' ctx f
| aexp_sexp' ctx (SVar x) = 
    let val consts = (Proof_Context.consts_of ctx)
        val {const_space, ...} = Consts.dest consts
        val lens = if (Name_Space.declared const_space x) then Const (x, dummyT) else Free (x, dummyT)
    in Const (@{const_name lens_get}, dummyT) $ lens $ Free (Lift_Expr.state_id, dummyT)
    end
| aexp_sexp' ctx (CVar x) = Free (x, dummyT);
in

fun sexp_aexp (Const (@{const_name SEXP}, _) $ Abs (_, _, e)) = sexp_aexp e
| sexp_aexp (Const (@{const_name lens_get}, _) $ n $ _) = SVar (Term.term_name n)
| sexp_aexp (Const (@{const_name zero_class.zero}, _)) = Num 0 
| sexp_aexp (Const (@{const_name one_class.one}, _)) = Num 1
| sexp_aexp (c as Const (@{const_name numeral}, _) $ _) = Num (snd (HOLogic.dest_number c))
| sexp_aexp (Const (n, _) $ e $ f) = BOp (n, sexp_aexp e, sexp_aexp f)
| sexp_aexp (Const (n, _) $ e) = UOp (n, sexp_aexp e)
| sexp_aexp (Free (n, _)) = CVar n;

fun aexp_sexp ctx e = Const (@{const_name "SEXP"}, dummyT) $ absfree (Lift_Expr.state_id, dummyT) (aexp_sexp' ctx e);

fun subst_ode ivar s = {ivar = ivar, odes = Symtab.map (fn _ => fn v => sexp_aexp v) (Expr_Util.subst_tab s)};

end

end