signature CONVERT_TO_SAGE =
sig
  val desolve : Arith_Expr.SODE -> string * string
  (*val getNumOutEqs: term -> int;*)
end;


structure Convert_To_Sage: CONVERT_TO_SAGE =
struct
local
  open Arith_Expr
in

exception SyntaxError of string;

  (* This removes things which are cannot be used in Python. Decoding is done in the Python
     conversion function *)
  fun encode_symbol x = if String.isPrefix ("\\" ^ "<") x then String.substring(x, 2, size(x) - 3) ^ "_SBL"
    else if String.isSuffix "_" x then String.substring(x, 0, size(x) - 1) else x;


  fun translate_term indep (BOp (name, lhs, rhs)) =
    let
      val printL = translate_term indep lhs
      and printR = translate_term indep rhs;
      fun printFun f = f ^ "(" ^ printL ^ "," ^ printR ^ ")";
      fun printOp op_ = "(" ^ printL ^ op_ ^ printR ^ ")";
    in
    case name of
        @{const_name "plus"} => printOp "+" 
      | @{const_name "minus"} => printOp "-"
      | @{const_name "divide"} => printOp "/"
      | @{const_name "times"} => printOp "*" 
      | @{const_name "power"} => printOp "**" 
      | @{const_name "powr"} => printOp "**" 
      | _ => raise SyntaxError name
    end |

  translate_term _ (NNat n) =
        Int.toString n |

  translate_term _ (NInt n) =
        Int.toString n |

  translate_term indep (UOp (name, arg)) =
    let
      val printV = translate_term indep arg;
      fun printFun f = f ^ "(" ^ printV ^ ")";
    in
      (case name of
            @{const_name "uminus"} => "-" ^ printV
          | @{const_name "ln"} => printFun "log" 
          | @{const_name "exp"} => printFun "exp" 
          | @{const_name "sin"} => printFun "sin" 
          | @{const_name "cos"} => printFun "cos" 
          | @{const_name "tan"} => printFun "tan" 
          | @{const_name "sinh"} => printFun "sinh" 
          | @{const_name "cosh"} => printFun "cosh" 
          | @{const_name "sqrt"} => printFun "sqrt" 
          | @{const_name "arcsin"} => printFun "arcsin" 
          | @{const_name "arccos"} => printFun "arccos" 
          | @{const_name "arctan"} => printFun "arctan" 
          | _ => raise SyntaxError name)
    end |
  translate_term _ (SVar x) = x |
  translate_term _ (CVar x) = x |
  translate_term _ _ = undefined ();

  fun get_consts (BOp (_, lhs, rhs)) = (get_consts lhs) @ (get_consts rhs) |
  get_consts (UOp (_, arg)) = get_consts arg |
  get_consts (CVar name) = [name] |
  get_consts _ = [];

  fun translate_sode {ivar = ivar, odes = odes} =
  let 
    val dvars = Symtab.keys odes
    val consts = (map (fn (_, ode) => get_consts ode) (Symtab.dest odes)) |> List.concat |> distinct (op =)
    val sage_dvars_declaration = map (fn dvar => dvar ^ " = function('" ^ dvar ^ "')(" ^ ivar ^ ")") dvars
    val derivatives = map (translate_term ivar o the o Symtab.lookup odes) (Symtab.keys odes)
    val sage_system_declarations = ListPair.map (fn (dvar, derivative) => "diff(" ^ dvar ^ "," ^ ivar ^ ") == " ^ derivative) (dvars, derivatives)
  in
    "free_vars = [" ^ (String.concatWith "," consts) ^ "];" ^
    ivar ^ " = var('" ^ ivar ^ "', domain='real');" ^
    (String.concatWith ";" sage_dvars_declaration) ^ ";" ^
    "odes = [" ^ (String.concatWith "," sage_system_declarations) ^ "];" ^
    "iVar = " ^ ivar ^ ";" ^
    "dVars = [" ^ (String.concatWith "," dvars) ^ "];" ^
    "SODE_solver = \\\"fricas\\\";" ^
    "ODE_solver = \\\"fricas\\\";" ^
    "preprocess_SODEs = True;"
  end;

  fun drop_last_char(s) = String.substring(s, 0, String.size(s) - 1);

  fun array_to_tuple([a, b]) = (a, b) |
      array_to_tuple(_) = undefined();

  val sageCommand = "sage";
  (*TODO: make this path not absolute*)
  val convertToIsabelleLocation = "/home/thomas/Documents/Paper/Isabelle-CAS-Integration/sage-integration/ConvertToIsabelle.py";

  (*
   desolve: solves the specified SODE using Sage.
   Returns: (a string of the solution, a string of the maximum domain of the solution)
  *)
  fun desolve sode =
    (Isabelle_System.bash_output (sageCommand ^ " -python " ^ convertToIsabelleLocation ^  " \"" ^
        (translate_sode sode) ^ "\""))
    |> #1
    |> drop_last_char
    |> (String.tokens (equal #"\n"))
    |> array_to_tuple;
end;
end;