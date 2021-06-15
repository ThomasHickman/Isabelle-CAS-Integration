(* Arithmetic Expressions for integration with CAS *)

signature ARITH_EXPR =
sig
datatype AExp =
  UOp of string * AExp |
  BOp of string * AExp * AExp |
  Num of int | 
  CVar of string |
  SVar of string;

type SODE = AExp Symtab.table;

val rev_conv: Symtab.key Symtab.table -> Symtab.key Symtab.table
val aexp_conv: string Symtab.table -> AExp -> AExp
val sode_conv: string Symtab.table -> SODE -> SODE

end

structure Arith_Expr: ARITH_EXPR =
struct

datatype AExp =
  UOp of string * AExp |
  BOp of string * AExp * AExp |
  Num of int | 
  CVar of string |
  SVar of string;

type SODE = AExp Symtab.table;

(* Reverse a conversion table *)
fun rev_conv cnv = Symtab.make (map (fn (x, y) => (y, x)) (Symtab.dest cnv))

fun aexp_conv cnv (UOp (n, e)) = UOp (n, aexp_conv cnv e)
| aexp_conv cnv (BOp (n, e, f)) = BOp (n, aexp_conv cnv e, aexp_conv cnv f)
| aexp_conv _ (Num n) = Num n
| aexp_conv cnv (CVar x) = (case Symtab.lookup cnv x of NONE => CVar x | SOME y => CVar y)
| aexp_conv cnv (SVar x) = (case Symtab.lookup cnv x of NONE => CVar x | SOME y => SVar y);

fun sode_conv cnv sode = 
  Symtab.make (map (fn (x, e) => (case Symtab.lookup cnv x of NONE => x | SOME y => y, aexp_conv cnv e)) (Symtab.dest sode));

end