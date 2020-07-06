theory ODE_Solve_Keyword
  imports
    "verification/ODE_extra"
  keywords "ode_solve" :: diag and "ode_solve_thm" :: thy_decl
begin

ML_file config.sml
ML_file "wolfram-integration/lex_mathematica.ML"
ML_file "wolfram-integration/parse_mathematica.ML"
ML_file "wolfram-integration/isabelle_to_mathematica.ML"
ML_file "wolfram-integration/mathematica_to_isabelle.ML"
ML_file "wolfram-integration/solve_ODE.ML"
ML_file "sage-integration/ConvertToSage.ML"


ML ‹
val DEBUGMODE = true;
fun my_tracing x = if DEBUGMODE then writeln x else ();

fun cartesian_power 1 = "ℝ" |
    cartesian_power n = cartesian_power (n-1) ^ " × ℝ"

(*NOTE: I can't get this function to work when it's in in ConvertToSage.ML, so I'm putting it here*)
fun get_ode_prop ctxt ode solver_name specified_domain specified_codomain = 
  let
    val ode_str = Syntax.pretty_term ctxt ode |> Pretty.string_of |> YXML.content_of;
    val (solution, max_domain) = desolve ode solver_name
        (Config.get ctxt ODE_solver_val) (Config.get ctxt preprocess_SODEs_val);
    val domain = if specified_domain = "" then max_domain else specified_domain;
    val codomain = if specified_codomain = "" then cartesian_power(getNumOutEqs ode) else specified_codomain;
    val final = "((" ^ solution ^ ") solves_ode (" ^ ode_str ^ ")) (" ^ domain ^ ") (" ^ codomain ^ ")"
  in final
end;

val SODE_solver_val = Attrib.setup_config_string @{binding "SODE_solver"} (K "fricas");

fun print_thm thm thm_name ctxt = 
  Proof_Display.print_results true (Position.thread_data ()) ctxt ((Thm.theoremK, thm_name), [("", [thm])]);

fun get_all_vars (Var ((name, _), _)) = [name]
  | get_all_vars (Const (_, _)) = []
  | get_all_vars (Free (name, _)) = [name]
  | get_all_vars (Bound _) = []
  | get_all_vars (Abs (name, _, t)) = cons name (get_all_vars t)
  | get_all_vars (t $ u) = append (get_all_vars t) (get_all_vars u);

fun prop_to_thm ctxt prop_str d_vars = 
  let
    val prop = Syntax.read_prop ctxt prop_str
    val ode_cert_tac = Method.NO_CONTEXT_TACTIC ctxt (
      Method_Closure.apply_method ctxt @{method ode_cert} [] [] [] ctxt [])
    val raw_thm = Goal.prove ctxt [] [] prop (K ode_cert_tac)
    val (_, ctxt1) = Variable.add_fixes d_vars ctxt
    val final_thm = singleton (Proof_Context.export ctxt1 ctxt) raw_thm
    in final_thm
end;

prop_to_thm @{context} "((λ t.((C0 :: real) * exp((t :: real)))) solves_ode (λt x. x)) (UNIV) (ℝ) " [];

fun generate_lemma lemma_txt binding attribs lthy = 
  let
    val ctxt = Local_Theory.target_of lthy
    val _ = writeln lemma_txt
    val vars = (Syntax.read_prop ctxt lemma_txt) |> get_all_vars |> distinct (op =)
    val thm = prop_to_thm ctxt (lemma_txt |> YXML.content_of) vars
    val _  = print_thm thm (Binding.name_of binding) ctxt
    in lthy |> (Local_Theory.note ((binding, []), [thm])) |> snd
  end;

fun do_ode_solve ctxt sode_text specified_domain specified_codomain =
  let val sode = Syntax.read_term ctxt sode_text in
  if (Config.get ctxt SODE_solver_val) = "wolfram" then
    Solve_ODE.solution_lemma sode |> Pretty.writeln
  else
    let val main_prop = get_ode_prop ctxt sode (Config.get ctxt SODE_solver_val) specified_domain specified_codomain in
    "lemma \"" ^ main_prop ^ "\" by ode_cert" |> writeln end
end;

fun do_ode_solve_thm sode_text binding attribs specified_domain specified_codomain lthy =
  let val ctxt = Local_Theory.target_of lthy
  val sode = Syntax.read_term ctxt sode_text
  val lemma_text = 
    if (Config.get ctxt SODE_solver_val) = "wolfram" then
      let val full_text = Solve_ODE.solution_lemma sode |> Pretty.string_of |> YXML.content_of in
      String.substring (full_text, 7, (String.size full_text - 22)) end (*get rid of the first and last parts of the theorem*)
    else
      (get_ode_prop ctxt sode (Config.get ctxt SODE_solver_val) specified_domain specified_codomain) ^ ""
  val _ = lemma_text;
  in generate_lemma lemma_text binding attribs lthy
end;


(*Test ode_solve_thm*)
val stm = "((λ t.(t^2 * 1/2 + x(0), y(0))) solves_ode (λ (t::real) (x, y). (t, 0))) {0..l} UNIV";
val prop = prop_to_thm @{context} stm;

Outer_Syntax.command \<^command_keyword>‹ode_solve› "Solves the input ode and prints a lemma with the solution"
    (Parse.term >> (fn sode_text => Toplevel.keep (fn st => 
      (do_ode_solve (Toplevel.context_of st) sode_text "" ""))));

Outer_Syntax.local_theory \<^command_keyword>‹ode_solve_thm› "Solves the input ode and proves the solution as a theorem"
    (((Parse_Spec.opt_thm_name ":") -- Parse.term -- (Scan.optional Parse.term "") -- (Scan.optional Parse.term "")) >> 
    (fn ((((binding, attribs), sode_text), domain), codomain) => 
      (do_ode_solve_thm sode_text binding attribs (domain |> YXML.content_of) (codomain |> YXML.content_of))));
›

end