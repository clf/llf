(* Identifier Translation During Parsing *)

signature VARS =
sig
  structure IntSyn : INTSYN

  val var : string * int -> (IntSyn.Exp * (IntSyn.Spine -> IntSyn.Exp)) 
end;
