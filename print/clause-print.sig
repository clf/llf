(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature CLAUSE_PRINT =
sig

  structure IntSyn : INTSYN
  structure Formatter : FORMATTER

  val formatClause : IntSyn.dctx * IntSyn.Exp -> Formatter.format
  (* val formatEntry : IntSyn.Entry -> Formatter.format *)

  val clauseToString : IntSyn.dctx * IntSyn.Exp -> string
  (* val entryToString : IntSyn.Entry -> string*)

end;  (* signature CLAUSE_PRINT *)
