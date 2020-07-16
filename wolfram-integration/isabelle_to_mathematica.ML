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
  val collect_bound: term -> string list
  val collect_free: term -> string list
  val translate_term: string list -> string Symtab.table -> term -> string
  val gen_fresh_bound: int -> string list
  val gen_fresh_free: string list -> string list -> string list
  val translate_ode: term -> string list -> string Symtab.table -> string
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
fun translate_term bound free (Const (name, _) $ lhs $ rhs) =
  let
    val printL = translate_term bound free lhs
    and printR = translate_term bound free rhs
    fun printFun f = f ^ "[" ^ printL ^ "," ^ printR ^ "]"
  in
  case name of
       @{const_name "plus"} => printFun "Plus" 
     | @{const_name "minus"} => "Plus[" ^ printL ^ ", Minus[" ^ printR ^"]]" 
     | @{const_name "divide"} => "Times[" ^ printL ^ ", Power[" ^ printR ^ ",-1]]" 
     | @{const_name "times"} => printFun "Times" 
     | @{const_name "power"} => printFun "Power" 
     | @{const_name "powr"} => printFun "Power" 
     | _ => raise SyntaxError name
  end |
(* Single argument functions *)
translate_term _ _ (Const (@{const_name "numeral"}, typ) $ arg) =
      Int.toString(snd(HOLogic.dest_number
          (Const (@{const_name "numeral"}, typ) $ arg)))|

translate_term bound free (Const (name, _) $ arg) =
  let
    val printV = translate_term bound free arg
    fun printFun f = f ^ "[" ^ printV ^ "]"
  in
    (case name of
          @{const_name "uminus"} => printFun "Minus" 
        | @{const_name "ln"} => printFun "Log" 
        | @{const_name "exp"} => printFun "Exp" 
        | @{const_name "sin"} => printFun "Sin" 
        | @{const_name "cos"} => printFun "Cos" 
        | @{const_name "tan"} => printFun "Tan" 
        | @{const_name "sinh"} => printFun "Sinh" 
        | @{const_name "cosh"} => printFun "Cosh" 
        | @{const_name "sqrt"} => "Power[" ^ printV ^ ", Rational[1,2]]" 
        | @{const_name "arcsin"} => printFun "ArcSin" 
        | @{const_name "arccos"} => printFun "ArcCos" 
        | @{const_name "arctan"} => printFun "ArcTan" 
        | _ => raise SyntaxError name)
  end |
(* Constants *)
translate_term _ _ (Const (name, _)) =
  ( case name of
    "Groups.one_class.one" => "1" |
    "Groups.zero_class.zero" => "0" | 
    _ => raise SyntaxError name) |
(* Bound variables *)
translate_term bound _ (Bound index) = nth bound index |
translate_term _ free (Free (name, _)) = Option.valOf (Symtab.lookup free name)

(* Obtain a list of variables bound in the term *)
fun collect_bound (Abs (a, _, c)) = a :: collect_bound c 
  | collect_bound (Const (_, _) $ a $ b) = collect_bound a @ collect_bound b 
  | collect_bound (Const (_, _) $ a) = collect_bound a 
  | collect_bound _ = []

fun collect_free' (Free (v, _)) = [v]
  | collect_free' (Const (_, _) $ a $ b) = collect_free' a @ collect_free' b
  | collect_free' (Const (_, _) $ a) = collect_free' a 
  | collect_free' (Abs (_, _, t)) = collect_free' t 
  | collect_free' _ = []

fun remove_duplicates [] = []
  | remove_duplicates (x::xs) = if exists (fn y => x = y) xs
                                   then remove_duplicates xs
                                   else x :: remove_duplicates xs

(* Need to remove duplicates in order to construct a Symtab *)
fun collect_free trm = (remove_duplicates o collect_free') trm


(* Obtain a list of the functions to be translated *)
fun collect_rhs trm =
  case trm of
       (Abs (_, _, rhs)) => collect_rhs rhs
     | (Const (@{const_name "case_prod"}, _) $ arg) => collect_rhs arg
     | (Const (@{const_name "Pair"}, _) $ l $ r) => l :: collect_rhs r
     | a => [a]
                           
fun repeat _ 0 = [] |
    repeat x n = x :: (repeat x (n-1))

(* Generate lexicographically ordered variables; used for translate_ode *) 
fun gen_fresh_bound count =
  Name.invent_list [] (String.implode (repeat #"a" (1 + count div 27))) count

(* Translation table from free variables to fresh ones, avoiding overlaps with
 * other fresh variables *)
fun gen_fresh_free frees bound =
  let
    val count = length frees
  in Name.invent_list bound
    (String.implode (repeat #"a" (1 + count div 27))) count
  (*in Symtab.make (ListPair.zipEq (fresh_frees, frees))*)
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
fun translate_ode ode bound_vars free_vars =
  let
    val indep::vars = bound_vars
    val mathematica_vars = map (fn x => x ^ ("[" ^ indep ^ "]")) vars
    val derivatives = map (translate_term
                            (rev (indep::mathematica_vars)) free_vars)
                            (collect_rhs ode)
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
