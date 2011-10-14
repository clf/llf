structure IntSyn =
  IntSyn (structure Global = Global);

structure Pattern =
  Pattern (structure IntSyn' = IntSyn);

(* Lazy lowering of EVar's can lead to problems in abstraction

structure WhnfLazy =
  Whnf (structure IntSyn' = IntSyn
	structure Pattern = Pattern); 
*)

structure Whnf =
 Whnf (structure IntSyn' = IntSyn
	structure Pattern = Pattern);

structure Normalize =
  Normalize (structure IntSyn' = IntSyn
	     structure Whnf = Whnf)

(* for debugging purposes only *)

structure Tools =
  Tools (structure IntSyn' = IntSyn
	 structure Normalize = Normalize
	 structure Whnf = Whnf)

structure Conv =
  Conv (structure IntSyn' = IntSyn
	structure Whnf = Whnf);

structure Constraints =
  Constraints (structure IntSyn' = IntSyn
	       structure Conv = Conv);

structure Trail = 
  Trail (structure IntSyn' = IntSyn);
  
structure NoTrail = 
  NoTrail (structure IntSyn' = IntSyn);

structure Unify =
  Unify (structure IntSyn' = IntSyn
	 structure Whnf = Whnf
	 structure Pattern = Pattern
	 structure Trail = NoTrail);

structure UnifyTrail =
  Unify (structure IntSyn' = IntSyn
	 structure Whnf = Whnf
	 structure Pattern = Pattern
	 structure Trail = Trail);

structure Abstract =
  Abstract (structure IntSyn' = IntSyn
	    structure Whnf = Whnf
	    structure Pattern = Pattern
	    structure Constraints = Constraints
	    structure Unify = Unify);
