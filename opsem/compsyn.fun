(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)

functor CompSyn (structure Global : GLOBAL
                 structure IntSyn' : INTSYN
		 structure Names : NAMES
		   sharing Names.IntSyn = IntSyn')
  : COMPSYN
  (* :> COMPSYN where IntSyn = IntSyn' *) =
struct

  structure IntSyn = IntSyn'


  datatype Goal =                       (* Goals                      *)
    Atom of IntSyn.Exp                  (* g ::= p                    *)
  | ATruth			        (*     | T                    *)
  | AConj of Goal * Goal		(*     | g1 & g2              *)
  | Lolli of ResGoal * IntSyn.Exp *	(*     | (r,A,h) -o g         *)
             IntSyn.cid * Goal		(*     A = uncompiled r       *)
  | Impl of ResGoal * IntSyn.Exp *      (*     | (r,A,h) => g         *)
            IntSyn.cid * Goal           (* h = target head of A  -ic? *)
  | All  of IntSyn.Dec * Goal           (*     | all x:A. g           *)

  and ResGoal =                         (* Residual Goals             *)
    Eq     of IntSyn.Exp                (* r ::= (p = ?)              *)
  | Zero				(*     | 0                    *)
  | Plus of ResGoal * ResGoal		(*     | r1 (+) r2            *)
  | Tensor of ResGoal * IntSyn.Exp * Goal  (*  | r (x) (A,g)          *)
  | And of ResGoal * IntSyn.Exp * Goal  (*     | r /\ (A,g)           *)
                                        (*     A is uncompiled g      *)
  | Exists of IntSyn.Dec * ResGoal      (*     | exists x:A. r        *)

  type Res = ResGoal * IntSyn.Sub * IntSyn.cid
  datatype Resource =
    Param				(* Parameter                  *)
  | Reusable of Res			(* Logical assumption         *)
  | Strict   of Res			(* Strict resource            *)
  | Lax      of Res			(* Lax resource               *)
  | Used     of Res			(* Consumed resource          *)

  (* The dynamic clause pool --- compiled version of the context *)
  type dpool = Resource IntSyn.Ctx

  (* Dynamic programs: context with synchronous clause pool, and
     lax and strict resources counters
     Invariant:
       If dProg = (G,dPool,st,lx)
       then G ~ dPool (context G matches dPool)
	    dPool contains st strict linear assumptions
	    dPool contains lx lax linear assumptions
  *)
  type dprog = IntSyn.dctx * dpool * int * int

  (* Linear constants *)
  datatype LinConTag =
    StrictCon				(* Strict linear constant    *)
  | LaxCon				(* Lax linear constant       *)
  | UsedCon				(* Used linear constant      *)

  (* Linear constants list, with number of strict and lax resource counters
     Invariant:
       If LC = (lCon,st,lx)
       then lCon contains st strict linear constants
	    lCon contains lx lax linear constants
  *)
  type linCon = (LinConTag * IntSyn.cid) IntSyn.Ctx * int * int

  val linCon = ref (IntSyn.Null : (LinConTag * IntSyn.cid) IntSyn.Ctx, 0, 0)

  (* The static program - compiled version of the signature *)
  datatype Entry =			(* Compiled signature Entry   *)
    SClause of ResGoal	                (* c : A : type               *)
  | Void 		                (* Other entries are ignored  *)

  local
    val maxCid = Global.maxCid
    val sProgArray = Array.array (maxCid+1, Void) : Entry Array.array
    val sProgLength  = ref(0)
  in
    (* Invariants *)
    (* if IntSyn.sgnArray(cid) =  IntSyn.ConstDec(_,_,_,Type),       *)
    (*   then sProgArray(cid) = SClause _                            *)
    (*   otherwise sProgArray(cid) = Void                            *)

    fun sProgAdd (entry) = 
        let
	  val cid = !sProgLength
	in
	  (* 0 <= cid < maxCid *)
	  (Array.update (sProgArray, cid, entry) ;
	   sProgLength := cid + 1;
	   cid)
	end

    (* 0 <= cid < !sProgSize *)
    fun sProgLookup (cid) = Array.sub (sProgArray, cid)
    fun sProgSize () = !sProgLength
    fun sProgReset () = (sProgLength := 0)
  end

  (* goalSub (g, s) = g'

     Invariants:
     If   G  |- s : G'    G' |- g : A
     then g' = g[s]
     and  G  |- g' : A
  *)
  fun goalSub (Atom P, s) = Atom(IntSyn.EClo(P,s))
    | goalSub (ATruth, s) = ATruth
    | goalSub (AConj(g1,g2), s) =
       AConj (goalSub (g1, s), goalSub (g2, s))
    | goalSub (Lolli(d, A, cid, g), s) =
       Lolli(resGoalSub (d, s),
	    IntSyn.EClo(A, s),
	    cid,
	    goalSub (g, IntSyn.ldot1 s))
    | goalSub (Impl(d, A, cid, g), s) =
       Impl(resGoalSub (d, s),
	    IntSyn.EClo(A, s),
	    cid,
	    goalSub (g, IntSyn.dot1 s))
    | goalSub (All(D,g), s) =
       All(IntSyn.decSub(D,s), goalSub (g, IntSyn.dot1 s))

  (* resGoalSub (r, s) = r'

     Invariants:
     If   G  |- s : G'    G' |- r : A
     then r' = r[s]
     and  G  |- r' : A [s]
  *)
  and resGoalSub (Eq Q, s) = Eq(IntSyn.EClo(Q,s))
    | resGoalSub (Zero, s) = Zero
    | resGoalSub (Plus (r1, r2), s) =
       Plus (resGoalSub (r1, s), resGoalSub (r2, s))
    | resGoalSub (Tensor(r, A, g), s) =
       Tensor(resGoalSub (r, IntSyn.ldot1 s),IntSyn.EClo(A,s), goalSub (g, s))
    | resGoalSub (And(r, A, g), s) =
       And(resGoalSub (r, IntSyn.dot1 s),IntSyn.EClo(A,s), goalSub (g, s))
    | resGoalSub (Exists(D, r), s) =
       Exists(IntSyn.decSub(D, s), resGoalSub (r, IntSyn.dot1 s))

end;  (* functor CompSyn *)
