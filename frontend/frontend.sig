(* Front End Interface *)
(* Author: Frank Pfenning *)

signature FRONT_END =
sig
  datatype Status = OK | ABORT
  val reset : unit -> unit
  val readFile : string -> Status
  val compile : unit -> unit

  type config
  val defineConfig : string list -> config
  val readConfig : config -> Status
  val compileConfig : config -> Status

  val top : unit -> unit
end;
