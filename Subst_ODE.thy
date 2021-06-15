section \<open> Substitutions as ODEs \<close>

theory Subst_ODE
  imports "Shallow-Expressions.Substitutions" "verification/ODE_extra"
begin

ML_file \<open>Arith_Expr.ML\<close>
ML_file \<open>Subst_ODE.ML\<close>
ML_file \<open>wolfram-integration/lex_mathematica.ML\<close>
ML_file \<open>wolfram-integration/parse_mathematica.ML\<close>
ML_file \<open>wolfram-integration/isabelle_to_mathematica.ML\<close>
ML_file \<open>wolfram-integration/mathematica_to_isabelle.ML\<close>

term "[x \<leadsto> 1, y \<leadsto> $x + $y]"

term "(\<notin>)"


ML \<open> 

  Syntax.check_term @{context} (Syntax.const "Set.not_member");

  open Isabelle_To_Mathematica;
  val sode = Subst_ODE.subst_ode @{term "[x \<leadsto> 1, y \<leadsto> $x]"};
  val out = mathematica_output
      (translate_sode "t" 
        (Arith_Expr.sode_conv (mk_var_conv sode) sode));
  Parse_Mathematica.parse out

\<close>

end