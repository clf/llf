(* Twelf             Copyright (c) 1997 by Carnegie Mellon University *)
(* Author: Frank Pfenning      <fp+@cs.cmu.edu>                       *)
(*         Carsten Schuermann  <carsten+@cs.cmu.edu>                  *)
(*         Iliano Cervesato    <iliano@cs.stanford.edu>               *)

(* Checking definitions for strictness                                *)

signature LINCHECK =
sig
  structure IntSyn : INTSYN
  structure Paths : PATHS

  exception Error of string
  exception Warning of string
  
  val linCheck: IntSyn.Exp * Paths.occExp option -> unit
  val linCheckEntry : IntSyn.Entry * Paths.occEntry -> unit
  val linCheckQuery : IntSyn.Exp * Paths.occExp -> unit
end;  (* signature LINCHECK *)
