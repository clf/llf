(* Timers collecting statistics about Twelf *)
(* Author: Frank Pfenning *)

functor Timers (structure Timing' : TIMING)
   : TIMERS
  (* :>  TIMERS where Timing = Timing' *) =
struct

  structure Timing = Timing'

  val parsing  = Timing.newCenter ("Parsing       ")
  val recon    = Timing.newCenter ("Reconstruction")
  val abstract = Timing.newCenter ("Abstraction   ")
  val checking = Timing.newCenter ("Checking      ")
  val modes    = Timing.newCenter ("Modes         ")
  val printing = Timing.newCenter ("Printing      ")
  val compiling= Timing.newCenter ("Compiling     ")
  val solving  = Timing.newCenter ("Solving       ")

  val centers = [parsing,recon,abstract,checking,modes,printing,compiling, solving]

  val total    = Timing.sumCenter ("Total         ", centers)

  val time = Timing.time

  fun reset () = List.app Timing.reset centers

  fun check () =
      (List.app (TextIO.print o Timing.toString) centers;
       TextIO.print (Timing.sumToString total);
       TextIO.print "Remember that the success continuation counts into Solving!\n")

  fun show () = (check (); reset ()) 

end;  (* functor Timers *)
