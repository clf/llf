(* Manipulating Constraints *)
(* Author: Jeff Polakow *)

signature CONSTRAINTS =
sig

   structure IntSyn : INTSYN

   val simplify : IntSyn.Eqn list -> IntSyn.Eqn list
   val warnConstraints : IntSyn.name list -> unit

end;  (* signature CONSTRAINTS *)
