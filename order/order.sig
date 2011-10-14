(* Termination Order *)
(* Author: Carsten Schuermann *)

signature ORDER =
sig

  structure IntSyn : INTSYN

  exception Error of string

  datatype Selector =			(* Selector for lex ordering  *)
      Nil				(* S ::= .                    *)
    | Select of int * Selector          (*     | member ord, S        *)

  datatype Mutual =			(* Termination ordering       *)
      Empty				(* O ::= No order specified   *)
    | LE of IntSyn.cid * Mutual		(*     | mutual dependencies  *)
    | LT of IntSyn.cid * Mutual		(*     | lex order for  -     *)

  datatype Order = 
      Order of Selector * Mutual
 
  val reset : unit -> unit
  val install : IntSyn.cid * Order -> unit 
  val lookup : IntSyn.cid -> Order
  val closure : IntSyn.cid -> IntSyn.cid list

end;  (* signature ORDER *)
