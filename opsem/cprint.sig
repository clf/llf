(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

signature CPRINT =
sig

  structure IntSyn: INTSYN
  structure CompSyn: COMPSYN

  val goalToString: IntSyn.dctx * CompSyn.Goal -> string
  val clauseToString: IntSyn.dctx * CompSyn.ResGoal -> string
  val sProgToString: unit -> string
  val dProgToString: CompSyn.dprog -> string
  val linConToString: CompSyn.linCon -> string

end; (* signature CPRINT *)
