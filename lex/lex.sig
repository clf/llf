(* Lexical Termination Declarations *)
(* Author: Carsten Schuermann *)

signature LEX =
sig
  structure LexSyn : LEXSYN

  exception  Error of string

  val install : LexSyn.Term -> unit 
end;

