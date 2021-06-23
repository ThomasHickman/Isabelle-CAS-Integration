(* Arithmetic Expressions for integration with CAS *)

signature ARITH_EXPR =
sig

(* Binder-free arithmetic expressions with an constants, state variables, and an independent variable *)

datatype AExp =
  UOp of string * AExp |
  BOp of string * AExp * AExp |
  NNat of int | 
  NInt of int |
  NReal of real |
  CVar of string | (* Constant *)
  SVar of string | (* State variable *)
  IVar; (* Independent variable *)

(* A system of ODEs consists of an independent variable a set of mappings from variable names to
  arithmetic expressions. *)

type SODE = {ivar: string, odes: AExp Symtab.table};

val foldl1_BOp: string -> AExp list -> AExp
val foldr1_BOp: string -> AExp list -> AExp
val rev_conv: Symtab.key Symtab.table -> Symtab.key Symtab.table
val aexp_conv: string Symtab.table -> AExp -> AExp
val sode_conv: string Symtab.table -> SODE -> SODE
val read_aexp: string -> AExp
val read_sol: string -> AExp Symtab.table

end

structure Arith_Expr  =
struct
local
  open Parse
in

datatype AExp =
  UOp of string * AExp |
  BOp of string * AExp * AExp |
  NNat of int | 
  NInt of int |
  NReal of real |
  CVar of string |
  SVar of string |
  IVar;

type SODE = {ivar: string, odes: AExp Symtab.table};

fun foldl1_BOp n = foldl1 (fn (x, y) => BOp (n, x, y));
fun foldr1_BOp n = foldr1 (fn (x, y) => BOp (n, x, y));

(* Reverse a conversion table *)
fun rev_conv cnv = Symtab.make (map (fn (x, y) => (y, x)) (Symtab.dest cnv))

fun aexp_conv cnv (UOp (n, e)) = UOp (n, aexp_conv cnv e)
| aexp_conv cnv (BOp (n, e, f)) = BOp (n, aexp_conv cnv e, aexp_conv cnv f)
| aexp_conv _ (NNat n) = NNat n
| aexp_conv _ (NInt n) = NInt n
| aexp_conv _ (NReal n) = NReal n
| aexp_conv cnv (CVar x) = (case Symtab.lookup cnv x of NONE => CVar x | SOME y => CVar y)
| aexp_conv cnv (SVar x) = (case Symtab.lookup cnv x of NONE => CVar x | SOME y => SVar y)
| aexp_conv _ IVar = IVar;

fun sode_conv cnv {ivar = ivar, odes = odes} = 
  {ivar = ivar, odes = Symtab.make (map (fn (x, e) => (case Symtab.lookup cnv x of NONE => x | SOME y => y, aexp_conv cnv e)) (Symtab.dest odes))};


fun parse_aexp xs =
  let open Parse
  in
  ((reserved "NNat" |-- Parse.int >> NNat)
  || (reserved "NInt" |-- Parse.int >> NInt)
  || (reserved "NReal" |-- Parse.real >> NReal)
  || (reserved "CVar" |-- Parse.string >> CVar)
  || (reserved "SVar" |-- Parse.string >> SVar)
  || (reserved "IVar" >> (fn _ => IVar))
  || (reserved "UOp" |-- $$$ "(" |-- Parse.string -- ($$$ "," |-- parse_aexp --| $$$ ")") >> UOp)
  || (reserved "BOp" |-- $$$ "(" |-- Parse.string -- ($$$ "," |-- parse_aexp) -- ($$$ "," |-- parse_aexp --| $$$ ")") >> (fn ((n, e), f) => BOp (n, e, f)))) xs
  end;

fun read_aexp xs = fst (parse_aexp (filter Token.is_proper (Token.explode (Thy_Header.get_keywords' @{context}) Position.none xs)));

val parse_sol = $$$ "[" |-- list ($$$ "(" |-- (string -- ($$$ "," |-- parse_aexp --| $$$ ")"))) --| $$$ "]";

fun read_sol xs = Symtab.make (fst (parse_sol (filter Token.is_proper (Token.explode (Thy_Header.get_keywords' @{context}) Position.none xs))));

end

end