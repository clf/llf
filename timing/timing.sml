(* Timing utilities based on SML'97 Standard Library *)
(* Author: Frank Pfenning *)

signature TIMING =
sig

  type center
  val newCenter : string -> center
  val reset : center -> unit
  val time : center -> ('a -> 'b) -> ('a -> 'b)

  type sum
  val sumCenter : string * center list -> sum

  val toString : center -> string
  val sumToString : sum -> string

end;  (* signature TIMING *)

structure Timing :> TIMING =
struct

  type cpuTime = {usr:Time.time, sys:Time.time, gc:Time.time}
  type realTime = Time.time

  datatype 'a result = Value of 'a | Exception of exn
  type center = string * (cpuTime * realTime) ref
  type sum = string * center list

  val zero = {usr = Time.zeroTime, sys = Time.zeroTime, gc = Time.zeroTime}

  fun minus ({usr = t1, sys = t2, gc = t3},
	     {usr = s1, sys = s2, gc = s3}) =
      {usr = Time.-(t1,s1), sys = Time.-(t2,s2), gc = Time.-(t3,s3)}

  fun plus ({usr = t1, sys = t2, gc = t3},
	    {usr = s1, sys = s2, gc = s3}) =
      {usr = Time.+(t1,s1), sys = Time.+(t2,s2), gc = Time.+(t3,s3)}

  fun sum ({usr = t1, sys = t2, gc = t3}) = Time.+ (t1, t2)

  local
    val CPUTimer = Timer.startCPUTimer ()
    val realTimer = Timer.startRealTimer ()
  in
    fun newCenter (name) = (name, ref (zero, Time.zeroTime))

    fun reset (_, counters) = (counters := (zero, Time.zeroTime))

    fun time (_, counters) (f:'a -> 'b) (x:'a) =
        let
	    val beginningRealTime = Timer.checkRealTimer (realTimer)
	    val beginningCPUTime = Timer.checkCPUTimer (CPUTimer)
	    val result = Value (f x) handle exn => Exception (exn)
	    val endCPUTime = Timer.checkCPUTimer (CPUTimer)
	    val endRealTime = Timer.checkRealTimer (realTimer)
	    val (CPUTime, realTime) = !counters
	    val _ = counters := (plus (CPUTime, (minus (endCPUTime, beginningCPUTime))),
				 Time.+ (realTime, (Time.- (endRealTime, beginningRealTime))))
	in
	  case result
	    of Value (v) => v
	     | Exception (e) => raise e
	end

    fun sumCenter (name, l) = (name, l)

    fun timesToString (name, (CPUTime as {usr = t1, sys = t2, gc = t3}, realTime)) =
        name ^ ": "
	^ "Real = " ^ (Time.toString realTime) ^ ", "
        ^ "Run = " ^ (Time.toString (sum CPUTime)) ^ " "
	^ "(" ^ Time.toString t1 ^ " usr + "
	^ Time.toString t2 ^ " sys, " ^ Time.toString t3 ^ " gc)"
	^ "\n"

    fun toString (name, ref (CPUTime, realTime)) = timesToString (name, (CPUTime, realTime))

    fun sumToString (name, centers) = 
        let fun sumup (nil, (CPUTime, realTime)) = timesToString (name, (CPUTime, realTime))
	      | sumup ((_, ref (C, R))::centers, (CPUTime, realTime)) =
	          sumup (centers, (plus (CPUTime, C), Time.+ (realTime, R)))
	in 
	  sumup (centers, (zero, Time.zeroTime))
	end

  end (* local ... *)
end;  (* structure Timing *)

