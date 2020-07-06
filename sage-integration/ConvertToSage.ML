fun iWrite(x) = x (*turn this off for production use*)

(*This removes things which are cannot be used in Python. Decoding is done in the Python conversion function*)
fun encode_symbol x = if String.isPrefix ("\\" ^ "<") x then String.substring(x, 2, size(x) - 3) ^ "_SBL" 
  else if String.isSuffix "_" x then String.substring(x, 0, size(x) - 1) else x;

fun convert_expression((Const (@{const_name "plus"}, _) $ a $ b, store)) = "(" ^ convert_expression(a, store) ^ "+" ^ convert_expression(b, store) ^ ")" |
convert_expression((Const (@{const_name "minus"}, _) $ a $ b, store)) = "(" ^ convert_expression(a, store) ^ "-" ^ convert_expression(b, store) ^ ")" |
convert_expression((Const (@{const_name "divide"}, _) $ a $ b, store)) = "(" ^ convert_expression(a, store) ^ "/" ^ convert_expression(b, store) ^ ")" |
convert_expression((Const (@{const_name "times"}, _) $ a $ b, store)) = "(" ^ convert_expression(a, store) ^ "*" ^ convert_expression(b, store) ^ ")" |
convert_expression((Const (@{const_name "uminus"}, _) $ a, store)) = "-" ^ convert_expression(a, store) |

convert_expression((Const (@{const_name "ln"}, _) $ arg, store))    = "ln(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "exp"}, _) $ arg, store))    = "exp(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "sin"}, _) $ arg, store))    = "sin(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "cos"}, _) $ arg, store))    = "cos(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "tan"}, _) $ arg, store))    = "tan(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "sinh"}, _) $ arg, store))   = "sinh(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "cosh"}, _) $ arg, store))   = "cosh(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "tanh"}, _) $ arg, store))   = "tanh(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "sqrt"}, _) $ arg, store))   = "sqrt(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "arcsin"}, _) $ arg, store))   = "arcsin(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "arccos"}, _) $ arg, store))   = "arccos(" ^ convert_expression(arg, store) ^ ")" |
convert_expression((Const (@{const_name "arctan"}, _) $ arg, store))   = "arctan(" ^ convert_expression(arg, store) ^ ")" |

convert_expression((Const (@{const_name "powr"}, _) $ arg1 $ arg2, store)) =  "(" ^ convert_expression(arg1, store) ^ "**" ^ convert_expression(arg2, store) ^ ")" |
convert_expression((Const (@{const_name "power"}, _) $ arg1 $ arg2, store)) =  "(" ^ convert_expression(arg1, store) ^ "**" ^ convert_expression(arg2, store) ^ ")" |


convert_expression (Const (@{const_name "numeral"}, t) $ a, _) = "Integer(" ^ Int.toString(snd(HOLogic.dest_number (Const (@{const_name "numeral"}, t) $ a))) ^ ")" |
convert_expression (Const (@{const_name "zero_class.zero"}, _), _) = "Integer(0)" |
convert_expression (Const (@{const_name "one_class.one"}, _), _) = "Integer(1)" |

convert_expression((Const (@{const_name "Pair"}, _) $ pair1 $ pair2, store)) = convert_expression(pair1, store) ^ "\n" ^ convert_expression(pair2, store) |

convert_expression((Bound a), store) = nth store a |> YXML.content_of|
convert_expression(Free (name, _), _) = name |> encode_symbol |
convert_expression (Const (name, _) $ _, _) = error ("Unknown type: " ^ name) |
convert_expression (x, _) = error "Unknown: " ^ (@{make_string} x);

fun get_frees (a $ b) = get_frees(a) @ get_frees(b) |
get_frees(Abs(_, _, rest)) = get_frees(rest) |
get_frees(Free(name, _)) = [name |> encode_symbol] |
get_frees _ = [];

fun read_sode(Abs(var, t, rest), store) = read_sode(rest, (var |> encode_symbol, t)::store) |
read_sode((Const (@{const_name "case_prod"}, _) $ x, store)) = read_sode(x, store) |
read_sode((Const (@{const_name "Pair"}, _) $ part1 $ part2, store)) = 
  {formulas=List.concat[#formulas (read_sode(part1, store)), #formulas (read_sode(part2, store))], vars=store} |
read_sode(x, store) = {formulas=[convert_expression(x, store |> (map #1))], vars=store}
(* where you want to indicate a genuine program error use the exceptionFail. *)
fun toSageType _ = "real";

fun getNumOutEqs x = read_sode(x, []) |> #formulas |> length;

fun desolve_text ode_ast SODE_solver ODE_solver preprocess_SODEs = 
  let val head_info = read_sode(ode_ast, [])
  val vars = head_info |> #vars |> rev
  val dVars = vars |> tl |> (map #1)
  val iVar = vars |> hd |> #1
  val iVarType = vars |> hd |> #2
  val frees = get_frees(ode_ast) |> distinct (op =) |> (map (fn x => "var('" ^ x ^ "', domain='real')"))
  val jCommar = String.concatWith ", " 
  val fullFormulas = head_info |> #formulas |> (curry ListPair.zip) dVars |>
     map (fn (dVar, formula) => "diff(" ^ dVar ^ ", " ^ iVar ^ ") == " ^ formula) |> jCommar
 in
    "free_vars = [" ^ jCommar frees ^ "];" ^
    iVar ^ " = var('" ^ iVar ^ "', domain='" ^ toSageType iVarType  ^ "');" ^
    jCommar dVars ^ " = " ^ jCommar (map (fn var => "function('" ^ var ^ "')(" ^ iVar ^ ")") dVars) ^ ";" ^
    "odes = [" ^ fullFormulas ^ "];" ^
    "iVar = " ^ iVar ^ ";" ^
    "dVars = [" ^ jCommar dVars ^ "];" ^
    "SODE_solver = \\\"" ^ SODE_solver ^ "\\\";" ^
    "ODE_solver = \\\"" ^ ODE_solver ^ "\\\";" ^
    "preprocess_SODEs = " ^ (if preprocess_SODEs then "True" else "False") ^ ";"
    |> iWrite end

fun drop_last_letter(s) = String.substring(s, 0, String.size(s) - 1)

fun array_to_tuple([a, b]) = (a, b) |
    array_to_tuple(_) = undefined();

val sageCommand = "sage"

fun desolve x SODE_solver ODE_solver preprocess_SODEs = 
  (Isabelle_System.bash_output (sageCommand ^ " -python " ^ convertToIsabelleLocation ^  " \"" ^ 
      (desolve_text x SODE_solver ODE_solver preprocess_SODEs) ^ "\""))
  |> #1
  |> drop_last_letter
  |> (String.tokens (equal #"\n"))
  |> array_to_tuple;

val ODE_solver_val = Attrib.setup_config_string @{binding "preprocess_ODE_solver"} (K "fricas");
val preprocess_SODEs_val = Attrib.setup_config_bool @{binding "preprocess_SODEs"} (K true);