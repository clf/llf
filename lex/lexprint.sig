(* Printer for Lexical Termination Declarations *)
(* Author: Carsten Schuermann *)

signature LEXPRINT =
sig
  structure LexSyn : LEXSYN

  val termToString : LexSyn.Term -> string
end;  (* signature LEXPRINT *)
