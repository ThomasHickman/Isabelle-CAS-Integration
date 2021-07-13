theory Tupled_ODE 
  imports ODE_Solve_Keyword
begin

ML_file \<open>Arith_Expr.ML\<close>
ML_file \<open>Tupled_ODE.ML\<close>

ML_file \<open>wolfram-integration/lex_mathematica.ML\<close>
ML_file \<open>wolfram-integration/parse_mathematica.ML\<close>
ML_file \<open>wolfram-integration/isabelle_to_mathematica.ML\<close>
ML_file \<open>wolfram-integration/mathematica_to_isabelle.ML\<close>
ML_file \<open>sage-integration/ConvertToSage.ML\<close>
(* Below is some code that could be used to call the Sage plugin *)

ML \<open> 
structure Solve_Tupled_ODE =
struct
  fun solve_tupled_ode ctx term =
  let
    open Isabelle_To_Mathematica; open Mathematica_To_Isabelle; open Tupled_ODE;
    val (vs, sode) = tupled_lam_ode term;
    val {ivar = ivar, ...} = sode
    val out = mathematica_output (translate_sode sode);
    val mexp = Parse_Mathematica.parse out;
    val rules = (map (map to_rule o to_list) o to_list) mexp;
    val tm = sol_tupled_lam ctx ivar vs (interpret_ode sode (hd rules))
  in Syntax.check_term ctx tm
  end;

  fun solve_tupled_ode_cmd ctx sode = 
    "Found ODE solution: " ^ Active.sendback_markup_command (Syntax.string_of_term ctx (solve_tupled_ode ctx sode)) |> writeln;

  fun solve_tupled_ode_cert_cmd ctx sode =
    "Found ODE solution: " 
      ^ Active.sendback_markup_command 
          ("lemma \"" ^ Syntax.string_of_term ctx 
            (Syntax.const @{const_name "solves_ode"} $ solve_tupled_ode ctx sode $ sode $ Syntax.const @{const_name top} $ Syntax.const @{const_name top})
           ^ "\" by ode_cert") 
    |> writeln;


end;
\<close>


(* Example call to the sage plugin *)

ML \<open>
val term = @{term "(\<lambda> t (x, y). (1, x))"};
open Tupled_ODE;
val (vs, sode) = tupled_lam_ode term;
val (x, y) = Convert_To_Sage.desolve sode;
writeln x
\<close>
ML \<open>
Arith_Expr.read_sol "[(\"x\", IVar), (\"y\", BOp (\"plus\", CVar \"1\", IVar))]"
\<close>


end