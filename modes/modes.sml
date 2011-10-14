structure Modes =
  Modes (structure IntSyn' = IntSyn
	 structure Table = IntRedBlackTree
	 structure Names = Names
	 structure Paths' = Paths);



structure IModePrint =
  ModePrint (structure IntSyn' = IntSyn
	       structure Names = Names
	       structure Modes' = Modes
	       structure Formatter = Formatter
	       structure Print = IPrint)

structure EModePrint =
  ModePrint (structure IntSyn' = IntSyn
	       structure Names = Names
	       structure Modes' = Modes
	       structure Formatter = Formatter
	       structure Print = EPrint)
