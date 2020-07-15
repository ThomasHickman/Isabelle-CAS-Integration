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
  val make_translation: string list -> string list -> string Symtab.table
  val get_domain: string -> rule list -> Parse_Mathematica.expr
  val interpret_odes: string list -> string list -> Parse_Mathematica.expr -> string list
  val interpret_ode: string list -> string Symtab.table -> rule list -> string
  exception TranslationError of string * Parse_Mathematica.expr
end

structure Mathematica_To_Isabelle : MATHEMATICA_TO_ISABELLE =
struct
(* Raised when the translation of an expression is not implemented *)
  local open Parse_Mathematica
  in
exception TranslationError of (string * expr)

datatype rule = Rule of string * expr
datatype ode_solution = Solution of rule list

(* Handle powers separately *)
fun translate_expr vars table (e as (Fun ("Power", args))) =
  (case args of
        [Id "E", exponent] => "exp(" ^ (translate_expr vars table exponent) ^ ")"
        (* ^ has type signature real -> nat -> real *)
      | [base, Int n] => let val trans_base = translate_expr vars table base
                         in (if n >= 0
                            then "(" ^ trans_base ^ " ^ " ^ translate_expr vars table (Int n) ^ ")" 
                            else "(1 / (" ^ trans_base ^ ") ^ " ^
                                translate_expr vars table (Int (~n)) ^ ")")
                         end
      | [base, exponent] => "(" ^ (translate_expr vars table base) ^ " powr "
                               ^ (translate_expr vars table exponent) ^ ")"
      | _ => raise TranslationError ("Invalid application of power", e)) |
translate_expr vars table (e as (Fun (fname, args))) =
  (case args of
    (* One parameter functions *)
    ([arg]) => (case fname of
                       "C" => let val Int n = arg in nth vars n end |
                       "Sin" => "sin(" ^ (translate_expr vars table arg) ^ ")"|
                       "Cos" => "cos(" ^ (translate_expr vars table arg) ^ ")" |
                       "Sinh" => "sinh(" ^ (translate_expr vars table arg) ^ ")" |
                       "Cosh" => "cosh(" ^ (translate_expr vars table arg) ^ ")" |
                       "Log" => "ln(" ^ (translate_expr vars table arg) ^ ")" |
                       _ => raise TranslationError ("Invalid function", e))|
    arglist => let val join_with = fn x => "(" ^ String.concatWith x (
                                     map (translate_expr vars table) arglist) ^ ")"
                 in (case fname of
                    (* Potentially many parameters *)
                    "Plus" => join_with " + " |
                    "Times" => join_with " * " |
                    "Or" => join_with "\<or>" |
                    (* Two parameters *)
                    "Rational" => join_with " / " |
                    "Unequal" => join_with "\<noteq>" |
                    "Equal" => join_with "=" |
                    "Greater" => join_with ">" |
                    "GreaterEqual" => join_with "\<ge>" |
                    "Less" => join_with "<" |
                    "LessEqual" => join_with "\<le>" |
                    _ => raise TranslationError ("Invalid function", e))
                 end |
    _ => raise TranslationError ("Invalid function", e)) | 
translate_expr vars table (Id v) = Option.getOpt ((Symtab.lookup table v), hd vars) | 
translate_expr _ _ (Int n) = if n < 0 then "-" ^ Int.toString (~ n)
                              else Int.toString n |
translate_expr _ _ (Real n) = if n < 0.0 then "-" ^ Real.toString (~ n)
                              else Real.toString n |
(* No functions that may be curried can be used in an ODE *)
translate_expr _ _ (CurryFun f) =
  raise TranslationError ("Invalid function", CurryFun f)


fun make_translation fresh_vars ode_vars =
  Symtab.make (ListPair.zipEq (fresh_vars, ode_vars))

(* Convert Mathematica Rules to (name, value) tuples *)
fun rule_to_tuple vars translations (Fun (_, [lhs,rhs])) =
  let val body = translate_expr vars translations rhs
      and Fun (parameter, _) = lhs
  in
    (Option.valOf (Symtab.lookup translations parameter), body)
  end

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

(* Takes a single ODE solution, in the form of a list of rules *)
fun interpret_ode vars translation rules =
  let val (source, target) =
      split_list (map (fn (Rule (param, rhs)) =>
                    ( Option.valOf (Symtab.lookup translation param)
                    , translate_expr vars translation rhs)
                    ) rules)
  in "\<lambda> (" ^ String.concatWith "," source ^ ") " ^ nth vars 0 ^ ". ("
     ^ String.concatWith "," target ^ ")"
  end

(* DSolve returns a list of solutions: map over them *)
fun interpret_odes ode_vars fresh_vars odes =
  let
    val translation = make_translation fresh_vars ode_vars 
    and rules = (map (map to_rule o to_list) o to_list) odes
  in map (interpret_ode ode_vars translation) rules
  end 
end
end
