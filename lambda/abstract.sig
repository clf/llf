(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature ABSTRACT =
sig
  structure IntSyn : INTSYN

  exception Error of string
    
  val raiseType : IntSyn.dctx * IntSyn.eclo -> IntSyn.Exp
  val piDepend  : (IntSyn.Dec * IntSyn.Depend) * IntSyn.Exp -> IntSyn.Exp

  val abstractDecl : IntSyn.Exp  -> (IntSyn.imp * IntSyn.Exp)
  val abstractDefn : (IntSyn.Exp * IntSyn.Exp) -> 
                       (IntSyn.imp * (IntSyn.Exp * IntSyn.Exp))
end;
