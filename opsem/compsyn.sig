(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)

signature COMPSYN =
sig

  structure IntSyn: INTSYN

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
     lax and strict resources counters *)
  type dprog = IntSyn.dctx * dpool * int * int
    (* add focus? speed up expected for programs with -o and -> mixed  -ic *)

  (* Linear constants *)
  datatype LinConTag =
    StrictCon				(* Strict linear constant    *)
  | LaxCon				(* Lax linear constant       *)
  | UsedCon				(* Used linear constant      *)

  (* Linear constants list, with number of strict and lax elements *)
  type linCon = (LinConTag * IntSyn.cid) IntSyn.Ctx * int * int
  (* not really a context, but ... oh well ... -ic *)

  val linCon : linCon ref

  (* Static programs --- compiled version of the signature *)
  datatype Entry =			(* Compiled signature Entry   *)
    SClause of ResGoal	                (* c : A : type               *)
  | Void 		                (* Other entries are ignored  *)

  val sProgAdd   : Entry -> IntSyn.cid
  val sProgLookup: IntSyn.cid -> Entry
  val sProgSize  : unit -> int
  val sProgReset : unit -> unit

  (* Explicit Substitutions *)

  val goalSub   : Goal * IntSyn.Sub -> Goal
  val resGoalSub: ResGoal * IntSyn.Sub -> ResGoal

end;  (* signature COMPSYN *)
