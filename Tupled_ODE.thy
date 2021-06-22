theory Tupled_ODE 
  imports "HOL.Transcendental"
begin

ML_file \<open>Arith_Expr.ML\<close>
ML_file \<open>Tupled_ODE.ML\<close>

ML_file \<open>wolfram-integration/lex_mathematica.ML\<close>
ML_file \<open>wolfram-integration/parse_mathematica.ML\<close>
ML_file \<open>wolfram-integration/isabelle_to_mathematica.ML\<close>
ML_file \<open>wolfram-integration/mathematica_to_isabelle.ML\<close>

ML \<open> 

structure Solve_Tupled_ODE =
struct
  fun solve_tupled_ode ctx term =
  let
    open Isabelle_To_Mathematica; open Mathematica_To_Isabelle; open Tupled_ODE;
    val (vs, sode) = tupled_lam_ode "t" term;
    val out = mathematica_output (translate_sode sode);
    val mexp = Parse_Mathematica.parse out;
    val rules = (map (map to_rule o to_list) o to_list) mexp;
    val tm = sol_tupled_lam ctx "t" vs (interpret_ode sode (hd rules))
  in Syntax.check_term ctx tm
  end;

  fun solve_subst_ode_cmd ctx sode = 
    "Found ODE solution: " ^ Active.sendback_markup_command (Syntax.string_of_term ctx (solve_tupled_ode ctx sode)) |> writeln;
end;
\<close>

end