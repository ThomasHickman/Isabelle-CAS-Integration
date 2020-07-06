(*  Title:      lex_mathematica.ML
    Author:     Christian Pardillo Laursen

 * Parser for tokenized Mathematica expressions
*) 
signature PARSE_MATHEMATICA =
sig
  datatype expr = Int of int
                | Real of real
                | Id  of string
                | Fun of string * expr list
                | CurryFun of string * expr list list
  val print_expr: expr -> string
  val parse: string -> expr
  exception SyntaxErr of string;
end;

structure Parse_Mathematica : PARSE_MATHEMATICA =
struct
  datatype expr = Int of int
                | Real of real
                | Id  of string
                | Fun of string * expr list
                | CurryFun of string * expr list list
  fun print_expr e =
    case e of
         (Id id) => id
       | (Fun (name, args)) => name ^ "[" ^ commas (map print_expr args) ^ "]"
       | (CurryFun (name, args)) => name ^
              (String.concat (map
                  (fn x => "[" ^ commas (map print_expr x) ^ "]")
                  args)) 
       | (Int n) => if n < 0 then "-" ^ Int.toString (~ n) else Int.toString n
       | (Real n) => if n < 0.0 then "-" ^ Real.toString (~ n) else Real.toString n 
  exception SyntaxErr of string;
  local
    open Scan;
    structure L = Lex_Mathematica;
  in 
    fun id toks = one (fn a => case a of L.Id _ => true | _ => false) toks; 
    fun value tks = one (fn a => case a of L.Punct _  => false
                                                 | _ => true) tks;
    fun punct p = one (fn x => case x of L.Punct a => a = p
                                       | _ => false);
    fun mkfun (L.Id a, [args]) = Fun (a, args)
      | mkfun (L.Id a, args) = CurryFun (a, args)
      | mkfun _ = raise SyntaxErr "Malformed function"

    fun mkval (L.Id a) = Id a
      | mkval (L.Real a) = Real a
      | mkval (L.Int a) = Int a
      | mkval _ = raise SyntaxErr "Unexpected value"

    fun expression toks =
      (((id (* Function name *) --
      (* Functions can be partially applied to several lists of arguments *)
      (repeat1 (permissive (punct "[" |-- 
      (* At least one argument - separate arguments with commas *)
      (repeat (expression --| punct ",") @@@ single expression)
      --| punct "]")))) >> mkfun)
      || (value >> mkval)) toks;

    fun parse a = case expression (L.scan a) of
                       (v, []) => v
                       (* ODEs must be represented as a single expression *)
                     | (_, _::_) => raise SyntaxErr "Extra characters in phrase"
end 
end
