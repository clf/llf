(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)

signature COMPILE =
sig

  structure IntSyn: INTSYN
  structure CompSyn: COMPSYN

  val compile: unit -> unit
  val compileGoal: IntSyn.Exp -> CompSyn.Goal

end; (* signature COMPILE *)