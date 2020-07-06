(*  Title:      isabelle_to_mathematica.ML
    Author:     Christian Pardillo Laursen

 * Translation from Isabelle terms to Mathematica expressions.
 * Used for solving ODEs via DSolve
 * 
 * The parameters for DSolve are:
 *   eqn: differential equation (or list of) to solve
 *   u: function or list of functions to solve for
 *   x: independent variable
*) 

signature ISABELLE_TO_MATHEMATICA =
sig
  val collect_vars: term -> string list
  val translate_term: string list -> term -> string
  val gen_vars: int -> string list
  val translate_ode: term -> string list -> string
  val mathematica_output: string -> string
  val collect_rhs : term -> term list
end

structure Isabelle_To_Mathematica: ISABELLE_TO_MATHEMATICA =
struct 

exception SyntaxError of string;

(* Translate the right-hand side of Isabelle terms to Mathematica functions
 * Arguments:
 *  variable names to be used for bound variables, in order of appearance
 *  term to be translated *)

(* Two-argument functions *)
fun translate_term vars (Const (name, _) $ lhs $ rhs) =
  let
    val printL = translate_term vars lhs
    and printR = translate_term vars rhs
    fun printFun f = f ^ "[" ^ printL ^ "," ^ printR ^ "]"
  in
  case name of
    @{const_name "plus"} => printFun "Plus" |
    @{const_name "minus"} => "Plus[" ^ printL ^ ", Minus[" ^ printR ^"]]" |
    @{const_name "divide"} => "Times[" ^ printL ^ ", Power[" ^ printR ^ ",-1]]" |
    @{const_name "times"} => printFun "Times" |
    @{const_name "power"} => printFun "Power" |
    _ => raise SyntaxError name
  end |
(* Single argument functions *)
translate_term _ (Const (@{const_name "numeral"}, typ) $ arg) =
      Int.toString(snd(HOLogic.dest_number
          (Const (@{const_name "numeral"}, typ) $ arg)))|

translate_term vars (Const (name, _) $ arg) =
  let
    val printV = translate_term vars arg
    fun printFun f = f ^ "[" ^ printV ^ "]"
  in
    (case name of
    @{const_name "uminus"} => printFun "Minus" |
    @{const_name "ln"} => printFun "Log" |
    @{const_name "exp"} => printFun "Exp" |
    @{const_name "sin"} => printFun "Sin" |
    @{const_name "cos"} => printFun "Cos" |
    @{const_name "sinh"} => printFun "Sinh" |
    @{const_name "cosh"} => printFun "Cosh" |
    @{const_name "sqrt"} => "Power[" ^ printV ^ ", Rational[1,2]]" |
    _ => raise SyntaxError name)
  end |
(* Constants *)
translate_term _ (Const (name, _)) =
  ( case name of
    "Groups.one_class.one" => "1" |
    "Groups.zero_class.zero" => "0" | 
    _ => raise SyntaxError name) |
(* Bound variables *)
translate_term vars (Bound index) = nth vars index

(* Obtain a list of variables bound in the term *)
fun collect_vars (Abs (a, _, c)) = a :: collect_vars c |
  collect_vars (Const (_, _) $ a $ b) = collect_vars a @ collect_vars b |
  collect_vars (Const (_, _) $ a) = collect_vars a |
  collect_vars _ = [];

(* Obtain a list of the functions to be translated *)
fun collect_rhs trm =
  case trm of
       (Abs (_, _, rhs)) => collect_rhs rhs |
       (Const (@{const_name "case_prod"}, _) $ arg) => collect_rhs arg |
       (Const (@{const_name "Pair"}, _) $ l $ r) => l :: collect_rhs r |
       a => [a]
                           
(* Generate lexicographically ordered variables; used in translate_ode *) 
fun gen_vars count =
  let fun repeat _ 0 = [] |
          repeat x n = x :: (repeat x (n-1))
  in Name.invent_list [] (String.implode (repeat #"a" (1 + count div 27))) count
  end

(* Taken from src/Tools/Metis/metis.ML *)
fun zipWith f =
    let
      fun z l [] [] = l
        | z l (x :: xs) (y :: ys) = z (f x y :: l) xs ys
        | z _ _ _ = raise SyntaxError "Unequal number of variables and derivatives";
    in
      fn xs => fn ys => List.rev (z [] xs ys)
    end;

(* Takes a list of variables to be used instead of those declared in the ODE.
 * This is done to ensure that the rules returned are ordered correctly, as
 * Mathematica orders them alphabetically. This also avoids name clashes.
 * Assumes the list has the exact amount of variables needed, and the first one
 * is the independent *)
fun translate_ode ode varnames =
  let
    val indep::vars = varnames
    val mathematica_vars = map (fn x => x ^ ("[" ^ indep ^ "]")) vars
    val derivatives = map (translate_term (rev (indep::mathematica_vars))) (collect_rhs ode)
    val mathematica_system = zipWith (fn x => fn y => x ^ "'[" ^ indep ^ "]==" ^ y) vars derivatives
  in "DSolve[{" ^ (String.concatWith "," mathematica_system) ^ "}, {" ^
                  (String.concatWith "," mathematica_vars) ^ "}, " ^
                  indep ^ "]"
  end

fun my_tracing x = let val _ = writeln x in x end

(* OutputForm forces it to display correctly, Quiet suppresses warnings ,
 * FullForm makes it easy to parse *)
fun mathematica_output(text) =
  fst (Isabelle_System.bash_output 
      ("echo \"OutputForm @ Quiet[FullForm[" ^ text ^ "]]\" | wolframscript -noprompt" |> my_tracing))
end
