(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

signature MODEPRINT =
sig
  structure Modes : MODES
  structure IntSyn : INTSYN

(*  val formatMode : string * Modes.ModeSpine -> Formatter.format 
   not yet implemented *)

  val modeToString : IntSyn.cid * Modes.ModeSpine -> string
end;  (* signature MODEPRINT *)
