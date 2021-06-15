theory ODE_Solve_Keyword
  imports
    "verification/ODE_extra"
  keywords "ode_solve" :: diag and "ode_solve_thm" :: thy_decl
begin

 
ML_file \<open>wolfram-integration/lex_mathematica.ML\<close>
ML_file \<open>wolfram-integration/parse_mathematica.ML\<close>
ML_file \<open>Arith_Expr.ML\<close>
ML_file \<open>wolfram-integration/isabelle_to_mathematica.ML\<close>
ML_file \<open>wolfram-integration/mathematica_to_isabelle.ML\<close>

(*
ML_file "wolfram-integration/mathematica_to_isabelle.ML"
ML_file "wolfram-integration/solve_ODE.ML"
ML_file "sage-integration/ConvertToSage.ML"
*)


end