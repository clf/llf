(* Normalization *)
(* Author: Carsten Schuermann *)

signature NORMALIZE =
sig
  structure IntSyn : INTSYN

  val normalize: IntSyn.eclo -> IntSyn.Exp
  val normalizeDec: IntSyn.Dec * IntSyn.Sub -> IntSyn.Dec
  val normalizeCtx: IntSyn.dctx -> IntSyn.dctx
end;  (* signature NORMALIZE *)
