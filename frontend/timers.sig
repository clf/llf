(* Timers collecting statistics about Twelf *)
(* Author: Frank Pfenning *)

signature TIMERS =
sig

  structure Timing : TIMING

  (* Programming interface *)
  val parsing  : Timing.center
  val recon    : Timing.center
  val abstract : Timing.center
  val checking : Timing.center
  val modes    : Timing.center
  val printing : Timing.center
  val compiling: Timing.center
  val solving  : Timing.center

  val total : Timing.sum

  val time : Timing.center -> ('a -> 'b) -> ('a -> 'b)

  (* External interface *)
  val reset : unit -> unit
  val check : unit -> unit
  val show : unit -> unit		(* check, then reset *)

end;  (* signature TIMERS *)
