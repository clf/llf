(* Indexing and Subordination *)
(* Author: Carsten Schuermann *)

signature INDEX =
sig
  structure IntSyn : INTSYN
    
  datatype Sgn = Empty | Entry of IntSyn.cid * Sgn

  val reset : unit -> unit
  val compile : unit -> unit
  val lookup : IntSyn.cid -> Sgn

  val <* : IntSyn.cid * IntSyn.cid -> bool
    (* transitive closure *)
  val == : IntSyn.cid * IntSyn.cid -> bool
  val << : IntSyn.cid * IntSyn.cid -> bool
    (* immediate subordination induced by a:K *)
(*  val < : IntSyn.cid * IntSyn.cid -> bool
    (* immediate subordination induced by c:A *) *)

  val get : IntSyn.cid -> string  list
end;

