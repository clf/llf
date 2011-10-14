(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature MODES =
sig
  structure IntSyn : INTSYN
  structure Paths : PATHS

  exception  Error of string

  datatype Mode = PlusPlus | Plus | Star | Minus |  MinusMinus  
  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and Marg = Marg of Mode * IntSyn.name option

  val reset : unit -> unit
  val calcImplicit : IntSyn.cid * ModeSpine * Paths.region -> ModeSpine
  val checkConsistency : IntSyn.cid * ModeSpine * Paths.region -> unit
 
  val installMode : (IntSyn.cid * ModeSpine) -> unit 
  val lookup : IntSyn.cid -> ModeSpine

  val checkD : IntSyn.cid * Paths.occEntry option -> unit	(* raises Error *)
  val checkG : IntSyn.Exp * Paths.occEntry option -> unit	(* raises Error *)
end;

