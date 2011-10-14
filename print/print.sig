(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

signature PRINT =
sig
  structure IntSyn : INTSYN
  structure Formatter : FORMATTER

  val printDepth : int option ref
  val printLength : int option ref

  val formatDec : IntSyn.dctx * IntSyn.Dec -> Formatter.format
  val formatExp : IntSyn.dctx * IntSyn.Exp -> Formatter.format
  val formatEntry : IntSyn.Entry -> Formatter.format

  val decToString : IntSyn.dctx * IntSyn.Dec -> string
  val expToString : IntSyn.dctx * IntSyn.Exp -> string
  val entryToString : IntSyn.Entry -> string

  val evarInstToString : (IntSyn.Exp * IntSyn.name) list -> string

end;  (* signature PRINT *)
