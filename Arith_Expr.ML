(* Arithmetic Expressions for integration with CAS *)

signature ARITH_EXPR =
sig
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

val foldl1_BOp: string -> AExp list -> AExp
val foldr1_BOp: string -> AExp list -> AExp
val rev_conv: Symtab.key Symtab.table -> Symtab.key Symtab.table
val aexp_conv: string Symtab.table -> AExp -> AExp
val sode_conv: string Symtab.table -> SODE -> SODE

end

structure Arith_Expr : ARITH_EXPR =
struct

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

end