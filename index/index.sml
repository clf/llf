structure Index =
  Index (structure Global = Global
	 structure IntSyn' = IntSyn
	 structure Whnf = Whnf
	 val SO = true)

structure IndexNoSO =
  Index (structure Global = Global
	 structure IntSyn' = IntSyn
         structure Whnf = Whnf
         val SO = false)
