structure TypeCheck =
  TypeCheck (structure IntSyn' = IntSyn
	     structure Conv = Conv
	     structure Whnf = Whnf
	     structure Print = IPrint);

structure Strictness =
  Strictness (structure IntSyn' = IntSyn);

structure LinCheck =
  LinCheck (structure IntSyn' = IntSyn
            structure Whnf = Whnf
	    structure Paths = Paths);
