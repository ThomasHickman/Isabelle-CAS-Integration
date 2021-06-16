section \<open> Substitutions as ODEs \<close>

theory Subst_ODE
  imports "Shallow-Expressions.Substitutions" "Hybrid-Library.Derivative_Lib"
begin

ML_file \<open>Arith_Expr.ML\<close>
ML_file \<open>Subst_ODE.ML\<close>
ML_file \<open>wolfram-integration/lex_mathematica.ML\<close>
ML_file \<open>wolfram-integration/parse_mathematica.ML\<close>
ML_file \<open>wolfram-integration/isabelle_to_mathematica.ML\<close>
ML_file \<open>wolfram-integration/mathematica_to_isabelle.ML\<close>

ML \<open> 

structure Solve_Subst_ODE =
struct
  fun solve_subst_ode ctx sode =
  let
    open Isabelle_To_Mathematica; open Mathematica_To_Isabelle; open Subst_ODE;
    val sode = subst_ode "t" sode;
    val out = mathematica_output (translate_sode sode);
    val mexp = Parse_Mathematica.parse out;
    val rules = (map (map to_rule o to_list) o to_list) mexp;
    val tm = ode_subst ctx "t" (interpret_ode sode (hd rules))
  in Syntax.check_term ctx tm
  end;

  fun solve_subst_ode_cmd ctx sode = 
    "Found ODE solution: " ^ Active.sendback_markup_command (Syntax.string_of_term ctx (solve_subst_ode ctx sode)) |> writeln;
end;
\<close>

end