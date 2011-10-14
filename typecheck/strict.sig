(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)

signature STRICTNESS =
sig
  structure IntSyn : INTSYN

  exception Error of string
  
  val check: IntSyn.Exp * IntSyn.Exp -> unit 
end;  (* signature STRICTNESS *)
