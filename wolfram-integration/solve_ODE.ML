(*  Title:      solve_ODE.ML
    Author:     Christian Pardillo Laursen

 * Implements the full workflow for solving ODEs in Isabelle
 * using an integration with Mathematica
*) 



signature SOLVE_ODE =
sig
  val get_mathematica_solution: term -> string
  val solve_ode: term -> string list
  val solution_lemma: term -> Pretty.T
end

structure Solve_ODE: SOLVE_ODE =
struct
local
  open Parse_Mathematica;
  open Isabelle_To_Mathematica;
  open Mathematica_To_Isabelle;
in 
  fun get_mathematica_solution ode =
    let
      val variables = collect_vars ode
      val fresh_vars = gen_vars (List.length variables)
    in mathematica_output (translate_ode ode fresh_vars)
    end

  fun solve_ode ode =
    let
      val variables = collect_vars ode
      val fresh_vars = gen_vars (List.length variables)
      val mat_sol = mathematica_output (translate_ode ode fresh_vars)
    in interpret_odes variables fresh_vars (parse mat_sol)
    end

  fun solution_lemma ode =
    let
      val variables = collect_vars ode
      val fresh_vars = gen_vars (List.length variables)
      val ast = parse (mathematica_output (translate_ode ode fresh_vars))
      val rules = hd ((map (map to_rule o to_list) o to_list) ast)
      val domain_expr = get_domain (hd fresh_vars) rules
      val domain = translate_expr variables domain_expr
      val translation = make_translation fresh_vars variables
      (* Parse it into a term to pretty print it later *)
      val solution_term = Proof_Context.read_term_pattern @{context}
                          (interpret_ode variables translation rules)
    in (case domain_expr of
          (* If domain is all of the reals don't include it *)
          Id _ => [Pretty.str "lemma \"((",
                   Syntax.pretty_term @{context} solution_term,
                   Pretty.str ")(",
                   Pretty.str (commas (tl variables)),
                   Pretty.str ") solves_ode (",
                   Syntax.pretty_term @{context} ode,
                   Pretty.str ")) T UNIV\" by (ode_cert)"]
         | _   => [Pretty.str "lemma \" ((",
                   Syntax.pretty_term @{context} solution_term,
                   Pretty.str ")(",
                   Pretty.str (commas (tl variables)),
                   Pretty.str ") solves_ode (",
                   Syntax.pretty_term @{context} ode,
                   Pretty.str ")) {",
                   Pretty.str (hd variables),
                   Pretty.str ". ",
                   Pretty.str domain,
                   Pretty.str "} UNIV\" by (ode_cert)"])
                |> Pretty.paragraph
    end 

end
end

