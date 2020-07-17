(*  Title:      solve_ODE.ML
    Author:     Christian Pardillo Laursen

 * Implements the full workflow for solving ODEs in Isabelle
 * using an integration with Mathematica
*) 



signature SOLVE_ODE =
sig
  val solution_lemma: term -> Pretty.T
end

structure Solve_ODE: SOLVE_ODE =
struct
local
  open Parse_Mathematica;
  open Isabelle_To_Mathematica;
  open Mathematica_To_Isabelle;
in 
  fun make_translation from to =
    Symtab.make (ListPair.zipEq (from, to))

  fun solution_lemma ode =
    let
      val bound = collect_bound ode
      val fresh_bound = gen_fresh_bound (List.length bound)
      val free = collect_free ode
      val fresh_free = gen_fresh_free free fresh_bound
      val free_table = make_translation free fresh_free
      val ast = parse (mathematica_output (translate_ode ode fresh_bound free_table))
      val rules = hd ((map (map to_rule o to_list) o to_list) ast)
      val fresh_vars = fresh_bound @ fresh_free
      val vars = bound @ free
      val translation = make_translation fresh_vars vars
      val domain_expr = get_domain (hd fresh_vars) rules
      val domain = translate_expr bound translation domain_expr
      (* Parse it into a term to pretty print it later *)
      val solution_term = Proof_Context.read_term_pattern @{context}
                          (interpret_ode bound translation rules)
    in (case domain_expr of
          (* If domain is all of the reals don't include it *)
          Id _ => [Pretty.str "lemma \"((",
                   Syntax.pretty_term @{context} solution_term,
                   Pretty.str ")(",
                   Pretty.str (commas (tl bound)),
                   Pretty.str ") solves_ode (",
                   Syntax.pretty_term @{context} ode,
                   Pretty.str ")) T UNIV\" by (ode_cert)"]
         | _   => [Pretty.str "lemma \" ((",
                   Syntax.pretty_term @{context} solution_term,
                   Pretty.str ")(",
                   Pretty.str (commas (tl bound)),
                   Pretty.str ") solves_ode (",
                   Syntax.pretty_term @{context} ode,
                   Pretty.str ")) {",
                   Pretty.str (hd bound),
                   Pretty.str ". ",
                   Pretty.str domain,
                   Pretty.str "} UNIV\" by (ode_cert)"])
                |> Pretty.paragraph
    end 

end
end

