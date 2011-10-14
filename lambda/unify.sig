(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature UNIFY =
sig

  structure IntSyn : INTSYN

  exception  Unify of string
	
  val unify : IntSyn.eclo * IntSyn.eclo -> unit	(* raises Unify *)
  val unifyW : IntSyn.eclo * IntSyn.eclo -> unit (* raises Unify *)
  val safeInvertExp : IntSyn.eclo * IntSyn.Sub -> IntSyn.Exp

end;  (* signature UNIFY *)
