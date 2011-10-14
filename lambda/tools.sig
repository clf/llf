(* Debugging Tools *)
(* Author: Carsten Schuermann *)

signature TOOLS =
sig
  structure IntSyn : INTSYN

  val stringExp : IntSyn.Exp -> string
  val stringSub : IntSyn.Sub -> string
  val stringCtx : IntSyn.dctx -> string
  val stringEntry: IntSyn.Entry -> string  
  val stringEntries: unit -> string  
  val stringSpine : IntSyn.Spine -> string
  val stringDec : IntSyn.Dec -> string
  val name : IntSyn.Exp option ref -> string
  val normalizeExp : IntSyn.eclo -> IntSyn.Exp
end;  (* signature TOOLS *)
