(* External Syntax of Lex Declarations *)
(* Author: Carsten Schuermann *)

signature LEXSYNEXT =
sig
  structure Paths : PATHS 

  type term

  val pi : (string list * term) -> term
  val body : (string * string option list * Paths.region) list -> term
end;  (* signature LEXSYNEXT *)


signature LEX_RECON =
sig
  structure LexSyn : LEXSYN
  include LEXSYNEXT

  exception Error of string
  val termToTerm : term -> LexSyn.Term
end;  (* signature LEX_RECON *)
