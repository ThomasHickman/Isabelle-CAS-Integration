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

  open Isabelle_To_Mathematica; open Mathematica_To_Isabelle; open Subst_ODE;
  val sode = Subst_ODE.subst_ode "t" @{term "[x \<leadsto> 1]"};
  val out = mathematica_output (translate_sode "t" sode);
(*
      (translate_sode "t"
        (Arith_Expr.sode_conv (mk_var_conv sode) sode));
*)
  val mexp = Parse_Mathematica.parse out;
  val rules = (map (map to_rule o to_list) o to_list) mexp;
  hd rules;
  interpret_ode sode (hd rules)

(*
val e = aexp_sexp @{context} (sexp_aexp @{term "get\<^bsub>x\<^esub> s + 5 + y"});
val e' = Syntax.check_term @{context} e;
(Syntax.string_of_term @{context} e) |> Active.sendback_markup_command |> writeln;
*)
\<close>

end