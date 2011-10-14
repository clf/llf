structure IPrint =
  Print (structure IntSyn' = IntSyn
	   structure Whnf = Whnf
	   structure Names = Names
	   structure Formatter' = Formatter
           val internal = true);

structure EPrint =
  Print (structure IntSyn' = IntSyn
	   structure Whnf = Whnf
	   structure Names = Names
	   structure Formatter' = Formatter
           val internal = false);

structure ClausePrint =
  ClausePrint (structure IntSyn' = IntSyn
		 structure Whnf = Whnf
		 structure Names = Names
		 structure Formatter' = Formatter
		 structure Print = EPrint);

