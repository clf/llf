(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)

functor Compile (structure IntSyn' : INTSYN
                  structure CompSyn' : COMPSYN
		    sharing CompSyn'.IntSyn = IntSyn')
  : COMPILE
  (* :> COMPILE
        where IntSyn = IntSyn'
        where CompSyn = CompSyn'
  *) =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  local
    structure I = IntSyn
    open CompSyn
  in

  (* CompileGoal A => G
     if A is a type interpreted as a subgoal in a clause and G is its
     compiled form.  No optimization is performed.
     Invariants:
     A is a fully reconstructed, fully expanded type
  *)
  fun compileGoal (r as I.Root _) = Atom r
    | compileGoal (I.Top)  = ATruth
    | compileGoal (I.With (A, B))  =
       AConj (compileGoal A, compileGoal B)
    | compileGoal (I.Pi((I.LDec(_,A), _), B)) =
       let
	 val cid = I.targetFam A                (* Change! -ic *)
       in
	 Lolli (compileClause A, A, cid, compileGoal B)
       (* The original antecedent is needed to build the proof-term.
	  The target Type of A is convenient for indexing
       *)
       end
    | compileGoal (I.Pi((I.Dec(_,A), I.No), B)) =
       let
	 val cid = I.targetFam A                (* Change! -ic *)
       in
	 Impl (compileClause A, A, cid, compileGoal B)
       (* The original antecedent is needed to build the proof-term.
	  The target Type of A is convenient for indexing
       *)
       end
    | compileGoal (I.Pi((d, I.Maybe),B)) =
       All (d, compileGoal B)
  (*  compileGoal _ should not arise by invariants *)

  (* CompileClause A => G
     if A is a type interpreted as a clause and G is its compiled form.
     No optimization is performed.
     Invariants:
     A is a fully reconstructed, fully expanded type
  *)
  and compileClause (r as I.Root _) = Eq r
    | compileClause (I.Top) = Zero
    | compileClause (I.With (A, B)) =
        Plus (compileClause A, compileClause B)
    | compileClause (I.Pi((d as (I.LDec(_,A)),_), B)) =
        Tensor (compileClause B, A, compileGoal A)
    | compileClause (I.Pi((d as (I.Dec(_,A)),I.No), B)) =
        And (compileClause B, A, compileGoal A)
    | compileClause (I.Pi((d,I.Maybe),B)) =
       Exists (d, compileClause B)
      (*  compileClause _ should not arise by invariants *)

  (* CompileEntry (E, fn (lCon,st) => LCon) = (fn (lCon,st) => LCon')
      Compiles signature entry E if it is an intuitionistic or linear
      constant, compiles it to Void otherwise.
      If   LCon (Null,0) = (lCon,st,0)
      and  LCon' (Null,0) = (lCon',st',0)
      and  E has cid c
      then st' = st+1 and LCon' = LCon @ (strictCon, c)   if E is linear
           st' = st   and LCon' = LCon                    otherwise
  *)
  fun compileEntry (I.ConstDec(_, _, A, I.Type), _, LCon) =
        (sProgAdd (SClause (compileClause A));
	 LCon)
    |  compileEntry (I.LinDec(_, _, A, I.Type), cid, LCon) =
	(sProgAdd (SClause (compileClause A));
	 fn (lCon,st) => LCon (I.Decl (lCon, (StrictCon,cid)), st+1))
    | compileEntry (_, _, LCon) =
	(sProgAdd (Void);
	 LCon)

  (* compile ()
      Compiles the entire signature and updates the linear constants pool
  *)
  fun compile () =
      let
	val size = I.sgnSize ()
	fun compile' (cid, LCon) =
	     if cid < size
	       then
		 compile' (cid+1, compileEntry (I.sgnLookup cid, cid, LCon))
	     else LCon (I.Null,0)
      in
	linCon := compile' (0, fn (lCon,st) => (lCon,st,0))
      end

  end  (* local open ... *)
end; (* functor Compile *)
