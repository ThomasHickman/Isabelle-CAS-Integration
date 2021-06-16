(*  Title:      mathematica_to_isabelle.ML
    Author:     Christian Pardillo Laursen

Translates parsed Mathematica expressions to Isabelle

Used for translating ODE solutions back into terms: raises
TranslationError whenever this assumption does not hold, or
some translation has not been implemented.
*)

signature MATHEMATICA_TO_ISABELLE =
sig
  type rule
  val to_rule : Parse_Mathematica.expr -> rule
  val to_list : Parse_Mathematica.expr -> Parse_Mathematica.expr list
  val translate_expr: string list -> string Symtab.table -> Parse_Mathematica.expr -> string
  val get_domain: string -> rule list -> Parse_Mathematica.expr
  val interpret_odes: string list -> string Symtab.table -> Parse_Mathematica.expr -> string list
  val interpret_ode: string list -> string Symtab.table -> rule list -> string
  exception TranslationError of string * Parse_Mathematica.expr
end

structure Mathematica_To_Isabelle =
struct
(* Raised when the translation of an expression is not implemented *)
  local open Parse_Mathematica; open Arith_Expr
  in
exception TranslationError of (string * expr)

datatype rule = Rule of string * expr
datatype ode_solution = Solution of rule list

(* Handle powers separately *)
fun translate_expr sode (e as (Fun ("Power", args))) =
  (case args of
        [Id "E", exponent] => UOp (@{const_name "exp"}, translate_expr sode exponent)
        (* ^ has type signature real -> nat -> real *)
      | [base, Int n] => let val trans_base = translate_expr sode base
                         in (if n >= 0
                            then BOp (@{const_name "power"}, trans_base, NNat n)
                            else if n = ~1 then BOp (@{const_abbrev inverse_divide}, NInt 1, trans_base)
                                  else BOp (@{const_name "power"}
                                           , BOp (@{const_name "divide"}, NInt 1, trans_base)
                                           , translate_expr sode (Int (~n))))
                         end
      | [base, exponent] => BOp (@{const_name powr}, translate_expr sode base, translate_expr sode exponent)
      | _ => raise TranslationError ("Invalid application of power", e)) |
translate_expr (sode as {ivar = _, odes = odes}) (e as (Fun (fname, args))) =
  (case args of
    (* One parameter functions *)
    ([arg]) => (case fname of
                     "C" => let val Int n = arg in SVar (nth (Symtab.keys odes) (n-1)) end
                   | "Sin" => UOp (@{const_name sin}, translate_expr sode arg)
                   | "Cos" => UOp (@{const_name cos}, translate_expr sode arg)
                   | "Tan" => UOp (@{const_name tan}, translate_expr sode arg) 
                   | "Sinh" => UOp (@{const_name sinh}, translate_expr sode arg) 
                   | "Cosh" => UOp (@{const_name cosh}, translate_expr sode arg) 
                   | "Tanh" => UOp (@{const_name tanh}, translate_expr sode arg) 
                   | "ArcSin" => UOp (@{const_name arcsin}, translate_expr sode arg)
                   | "Log" => UOp (@{const_name ln}, translate_expr sode arg) 
                   | _ => raise TranslationError ("Invalid one-paramter function", e))
  | arglist => let val join_with = fn x => foldl1_BOp x (map (translate_expr sode) arglist)
                 in (case fname of
                    (* Potentially many parameters *)
                          "Plus" => join_with @{const_name plus} 
                        | "Times" => join_with @{const_name times} 
                        | "Or" => join_with @{const_name disj} 
                        | "And" => join_with @{const_name conj}  
                        | "NotElement" => join_with @{const_abbrev Set.not_member} 
(*                        | "Inequality" => (* Inequalities are of the form Inequality[a,<=,b,<=,c] *)
                            let fun transl x = translate_expr sode x
                            and handle_inequality (a::b::c::l) =
                                (transl a) ^ (transl b) ^ (transl c) ^
                                (case l of [] => "" | _ => " \<and> " ^ handle_inequality (c::l))
                            in handle_inequality arglist
                            end *)
                        (* Two parameters *)
                        | "Rational" => join_with @{const_name divide}
                        | "Element" => join_with @{const_name "Set.member"}
                        | "Unequal" => join_with @{const_abbrev HOL.not_equal}
                        | "Equal" => join_with @{const_name "HOL.equal"}
                        | "Greater" => join_with @{const_abbrev greater}
                        | "GreaterEqual" => join_with @{const_abbrev greater_eq}
                        | "Less" => join_with @{const_name less}
                        | "LessEqual" => join_with @{const_name less_eq}
                        | _ => raise TranslationError ("Invalid multi-parameter function", e))
                 end)

(*
 |
translate_expr vars table (e as (Fun (fname, args))) =
  (case args of
    (* One parameter functions *)
    ([arg]) => (case fname of
                     "C" => let val Int n = arg in nth vars n end
                   | "Sin" => "sin(" ^ (translate_expr vars table arg) ^ ")"
                   | "Cos" => "cos(" ^ (translate_expr vars table arg) ^ ")" 
                   | "Tan" => "tan(" ^ (translate_expr vars table arg) ^ ")" 
                   | "Sinh" => "sinh(" ^ (translate_expr vars table arg) ^ ")" 
                   | "Cosh" => "cosh(" ^ (translate_expr vars table arg) ^ ")" 
                   | "Tanh" => "tanh(" ^ (translate_expr vars table arg) ^ ")" 
                   | "ArcSin" => "arcsin(" ^ (translate_expr vars table arg) ^ ")" 
                   | "Log" => "ln(" ^ (translate_expr vars table arg) ^ ")" 
                   | _ => raise TranslationError ("Invalid one-paramter function", e))
  | arglist => let val join_with = fn x => "(" ^ String.concatWith x (
                                     map (translate_expr vars table) arglist) ^ ")"
                 in (case fname of
                    (* Potentially many parameters *)
                          "Plus" => join_with " + " 
                        | "Times" => join_with " * " 
                        | "Or" => join_with "\<or>" 
                        | "And" => join_with "\<and>" 
                        | "NotElement" => join_with "\<notin>" 
                        | "Inequality" => (* Inequalities are of the form Inequality[a,<=,b,<=,c] *)
                            let fun transl x = translate_expr vars table x
                            and handle_inequality (a::b::c::l) =
                                (transl a) ^ (transl b) ^ (transl c) ^
                                (case l of [] => "" | _ => " \<and> " ^ handle_inequality (c::l))
                            in handle_inequality arglist
                            end
                        (* Two parameters *)
                        | "Rational" => join_with " / "
                        | "Element" => join_with " \<in> "
                        | "Unequal" => join_with "\<noteq>"
                        | "Equal" => join_with "="
                        | "Greater" => join_with ">"
                        | "GreaterEqual" => join_with "\<ge>"
                        | "Less" => join_with "<"
                        | "LessEqual" => join_with "\<le>"
                        | _ => raise TranslationError ("Invalid multi-parameter function", e))
                 end) |
*) |
translate_expr {ivar = ivar, odes = odes} (Id v) =
      (case v of
(*          "LessEqual" => " \<le> "
        | "Less" => " < "
        | "GreaterEqual" => " \<ge> "
        | "Greater" => " > "
        | "Unequal" => " \<noteq> "
        | "Integers" => "\<int>"
*)
        _ => if Ord_List.member string_ord (Symtab.keys odes) v
               then SVar v 
               else if (v = ivar) 
               then IVar
               else CVar v) |
translate_expr _ (Int n) = NInt n 
(*
|
translate_expr _ (Real n) = if n < 0.0 then "-" ^ Real.toString (~ n)
                            else Real.toString n *)
(*
(* No functions that may be curried can be used in an ODE *)
translate_expr _ _ (CurryFun f) =
  raise TranslationError ("Invalid function", CurryFun f)
*)
(* Read a Rule expression into the Rule datatype *)
fun to_rule (Fun (fname, [lhs, rhs])) =
  if fname = "Rule"
  then (case lhs of
       (* Lhs is represented as a function of the independent for ODEs *)
       Fun (parameter,_) => Rule (parameter, rhs)
     | _ => raise TranslationError ("Invalid rule lhs", lhs))
  else raise TranslationError ("Expected Rule", (Fun (fname, [lhs,rhs])))
| to_rule r = raise TranslationError ("Expected two-argument rule", r)

fun to_list (x as Fun (f, l)) =
      if f = "List" then l
      else raise TranslationError ("Expected List", x)

(* Retrieve the domain of a list of rules given independent var *)
fun get_domain indep rules =
  let
    val fns = map (fn (Rule (_,x)) => print_expr x) rules
    val mathematica_query = "FunctionDomain[{" ^ (commas fns) ^ "}," ^ indep ^ "]"
    val response = Isabelle_To_Mathematica.mathematica_output(mathematica_query)
  in parse response
  end

fun rule_ordering (Rule (a,_), Rule (b, _)) = String.compare (a, b)

(* Question: Does the ordering of rules really matter now that ODEs are ordered maps? *)


(* Takes a single ODE solution, in the form of a list of rules *)
fun interpret_ode sode rules =
(*   let val (source, target) = *)
      Symtab.make (
      map (fn (Rule (param, rhs)) =>
              ( param
              , translate_expr sode rhs)
              ) (sort rule_ordering rules))
  (*
  in (source, target) (* source = name of variable, target = expression *)
     (* "\<lambda> (" ^ String.concatWith "," source ^ ") " ^ nth vars 0 ^ ". ("
     ^ String.concatWith "," target ^ ")" *)
  end
  *)

(*
fun my_tracing x = let val _ = writeln x in x end
(* DSolve returns a list of solutions: map over them *)
fun interpret_odes bound_vars free_translation odes =
  let
    val rules = (map (map to_rule o to_list) o to_list) odes
  in map (interpret_ode bound_vars free_translation) rules
  end
*)

end
end
