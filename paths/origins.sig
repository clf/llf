(* Origins of Declarations *)
(* Author: Frank Pfenning *)

signature ORIGINS =
sig

  structure IntSyn : INTSYN
  structure Paths : PATHS

  (* val reset : unit -> unit *)
  val installOrigin : IntSyn.cid * Paths.occEntry option -> unit
  val originLookup : IntSyn.cid -> Paths.occEntry option

end;  (* signature ORIGINS *)
