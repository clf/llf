(* Parsing Lex Declarations *)
(* Author: Carsten Schuermann *)

signature PARSE_LEX =
sig

  structure Parsing : PARSING
  structure LexSynExt: LEXSYNEXT

  val parseLex' : LexSynExt.term Parsing.parser

end;  (* signature PARSE_LEX *)
