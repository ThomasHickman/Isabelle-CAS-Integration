(*  Title:      lex_wolfram.ML
    Author:     Christian Pardillo Laursen

 * Lexer for Wolfram FullForm expressions.
*) 

signature LEX_WOLFRAM =
sig
  datatype token = Id of string | Punct of string | Int of int | Real of real;
  val scan : string -> token list
end;

structure Lex_Wolfram: LEX_WOLFRAM =
struct
  datatype token = Id of string | Punct of string | Int of int | Real of real;

  fun scanNum ss =
    let
      (*called after the decimal point*)
      fun scanReal (acc, ss) =
        let
          val (n, tail) = Substring.splitl Char.isDigit ss
        in
          (Real (Option.valOf (Real.fromString (acc ^ Substring.string (n)))), tail)
        end;
      val (num, ss1) = Substring.splitl (fn x => Char.isDigit x orelse x = #"-") ss
    in
      case Substring.getc ss1 of
              (* End of string *)
              NONE => (Int (Option.valOf (Int.fromString (Substring.string num))), ss)
              (* Decimal point *)
            | SOME (#".", ss1) => scanReal ((Substring.string num) ^ ".", ss1)
              (* End of number *)
            | _ => (Int (Option.valOf (Int.fromString (Substring.string num))), ss1)
    end;

  (*Scanning a substring into a list of tokens*)
  fun scanning (toks, ss) = 
      case Substring.getc ss of
	  NONE => rev toks    (*end of substring*)
	| SOME (c,ss1) => 
	    if Char.isAlpha c 
		  then (*identifier*)
		   let val (id, ss2) = Substring.splitl Char.isAlphaNum ss
		       val tok = Id (Substring.string id)
		   in  scanning (tok::toks, ss2)
		   end
		   else if Char.isDigit c orelse c = #"-"
          then (*number*)
            let val (tok, ss1) = scanNum ss
            in scanning (tok::toks, ss1)
            end
	    else if Char.isPunct c
	      then (*special symbol*)
		   let val tok = Punct (String.str c)
		   in  scanning (tok::toks, ss1)
		   end
       
	    else (*ignore spaces, line breaks, control characters*)
		 scanning (toks, Substring.dropl (not o Char.isGraph) ss);

  fun scan a = scanning([], Substring.full a);
end; 
