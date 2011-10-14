(* Pattern Substitutions *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature PATTERN = 
sig
  structure IntSyn : INTSYN

  val checkSub : IntSyn.Sub -> bool
  val dotEta   : IntSyn.Head * IntSyn.Sub -> IntSyn.Sub
  val ldotEta  : IntSyn.Head * IntSyn.Sub -> IntSyn.Sub
  val etaContract : IntSyn.Exp -> int
end;  (* signature PATTERN *)
