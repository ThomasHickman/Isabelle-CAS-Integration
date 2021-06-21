theory Tupled_ODE 
  imports "HOL.Transcendental"
begin

ML_file \<open>Arith_Expr.ML\<close>
ML_file \<open>Tupled_ODE.ML\<close>

ML \<open>

Tupled_ODE.tupled_lam_ode @{term "\<lambda> (x, y). (1, x)"};

HOLogic.strip_tuple (fst (dest_tupled_lambda (HOLogic.tupled_lambda @{term "(x, y)"} @{term "x"})));

\<close>



end