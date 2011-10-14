(* Weak Head-Normal Forms *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature WHNF =
sig
    structure IntSyn : INTSYN

    val whnf : IntSyn.eclo -> IntSyn.eclo
    val expandDefn : IntSyn.eclo -> IntSyn.eclo
    val etaExpandRoot : IntSyn.Exp -> IntSyn.Exp
end; (* signature WHNF *)
