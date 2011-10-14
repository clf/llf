(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

functor CPrint (structure IntSyn' : INTSYN
                  structure CompSyn' : COMPSYN
		    sharing CompSyn'.IntSyn = IntSyn'
		  structure Print: PRINT
		    sharing Print.IntSyn = IntSyn'
		  structure Formatter : FORMATTER
		    sharing Print.Formatter = Formatter
		  structure Names: NAMES
		    sharing Names.IntSyn = IntSyn')
  : CPRINT
  (* :> CPRINT
        where IntSyn = IntSyn'
        where CompSyn = CompSyn'
  *) =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  open CompSyn

  fun goalToString (G, Atom(p)) =
       "\tSOLVE  " ^ Print.expToString (G, p) ^ "\n"
    | goalToString (G, ATruth) =
       "\tDISCARD\n"
    | goalToString (G, AConj (g1, g2)) =
       goalToString (G, g1) ^
       "\tTOGETHER WITH\n" ^
       goalToString (G, g2)
    | goalToString (G, Lolli (_,A,_,g)) =
       "\tLINEARLY ASSUME " ^ Print.expToString (G, A) ^ "\n" ^
       goalToString (IntSyn.Decl(G, IntSyn.LDec(NONE, A)), g) ^ "\n"
    | goalToString (G, Impl (_,A,_,g)) =
       "\tASSUME " ^ Print.expToString (G, A) ^ "\n" ^
       goalToString (IntSyn.Decl(G, IntSyn.Dec(NONE, A)), g) ^ "\n"
    | goalToString (G, All(D,g)) =
       let
	 val D' = Names.decName (G, D)
       in
	 "\tALL    " ^
	 Formatter.makestring_fmt (Print.formatDec (G, D')) ^ "\n" ^
	 goalToString (IntSyn.Decl (G, D'), g) ^ "\n"
       end

  fun clauseToString (G, Eq(p)) =
       "\tUNIFY  " ^ Print.expToString (G, p) ^ "\n"
    | clauseToString (G, Zero) = "\tFAIL\n"
    | clauseToString (G, Plus (r1, r2)) =
       clauseToString (G, r1) ^
       "\tOR ALTERNATIVELY\n" ^
       clauseToString (G, r2)
    | clauseToString (G, Tensor(r, A, g)) =
       clauseToString (IntSyn.Decl(G, IntSyn.LDec(NONE, A)), r) ^
       goalToString (G, g)
    | clauseToString (G, And(r, A, g)) =
       clauseToString (IntSyn.Decl(G, IntSyn.Dec(NONE, A)), r) ^
       "INT" ^
       goalToString (G, g)
    | clauseToString (G, Exists(D, r)) =
       let
	 val D' = Names.decName (G, D)
       in
	 "\tEXISTS " ^
	 Print.decToString (G, D') ^ "\n" ^
         clauseToString (IntSyn.Decl(G, D'), r)
       end

(* Does not take grouping of different constructs into account.  Change
   drastically.  -ic *)

  fun entryToString (cid, SClause(r)) = 
      let
	val _ = Names.varReset ()
	val e = IntSyn.sgnLookup cid
	val c = IntSyn.entryName e
	val l = String.size c
      in
	case e
	  of IntSyn.LinDec _ =>
	    (c ^ (if l > 6 then "^\n" else "^") ^
	     clauseToString (IntSyn.Null, r) ^ "\n")
	   | _ =>
	    (c ^ (if l > 6 then ":\n" else ":") ^
	     clauseToString (IntSyn.Null, r) ^ "\n")
      end
    | entryToString (cid, Void) =
        Print.entryToString (IntSyn.sgnLookup cid) ^ "\n\n"

  fun sProgToString () = 
      let val size = CompSyn.sProgSize ()
	  fun ts (cid) = if cid < size
			   then entryToString (cid, CompSyn.sProgLookup cid)
			        ^ ts (cid+1)
			 else ""
       in
	 ts 0
       end

  fun dProgToString (G, dPool, st, lx) =
    let
      fun dpts (IntSyn.Null, IntSyn.Null) = ""
	| dpts (IntSyn.Decl(G,IntSyn.Dec(SOME x,_)),
		IntSyn.Decl(dPool,Reusable(r,_,_))) =
	  dpts (G, dPool) ^
	  "Clause    " ^ x ^ ":\t" ^
	  clauseToString (G, r)
	| dpts (IntSyn.Decl(G,IntSyn.Dec(NONE,_)),
		IntSyn.Decl(dPool,Reusable(r,_,_))) =
	  dpts (G, dPool) ^
	  "Clause    _:\t" ^
	  clauseToString (G, r)
	| dpts (IntSyn.Decl(G, IntSyn.Dec(SOME x,A)),
		     IntSyn.Decl(dPool, Param)) =
	  dpts (G, dPool) ^
	  "Parameter " ^ x ^ ":\t" ^
	  Print.expToString (G, A)
	| dpts (IntSyn.Decl(G, IntSyn.Dec(NONE,A)),
		IntSyn.Decl(dPool, Param)) =
	  dpts (G, dPool) ^
	  "Parameter _:\t" ^
	  Print.expToString (G, A)
	| dpts (IntSyn.Decl(G,IntSyn.LDec(SOME x,_)),
		IntSyn.Decl(dPool,Strict(r,_,_))) =
	  dpts (G, dPool) ^
	  "Clause (S) " ^ x ^ "^\t" ^
	  clauseToString (G, r)
	| dpts (IntSyn.Decl(G,IntSyn.LDec(NONE,_)),
		IntSyn.Decl(dPool,Strict(r,_,_))) =
	  dpts (G, dPool) ^
	  "Clause (S) _^\t" ^
	  clauseToString (G, r)
	| dpts (IntSyn.Decl(G, IntSyn.LDec(SOME x,A)),
		IntSyn.Decl(dPool, Lax(r,_,_))) =
	  dpts (G, dPool) ^
	  "Clause (L) " ^ x ^ "^\t" ^
	  clauseToString (G, r)
	| dpts (IntSyn.Decl(G, IntSyn.LDec(NONE,A)),
		IntSyn.Decl(dPool, Lax(r,_,_))) =
	  dpts (G, dPool) ^
	  "Clause (L) _^\t" ^
	  clauseToString (G, r)
	| dpts (IntSyn.Decl(G, IntSyn.LDec(SOME x,A)),
		IntSyn.Decl(dPool, Used(r,_,_))) =
	  dpts (G, dPool) ^
	  "Clause (U) " ^ x ^ "^\t" ^
	  clauseToString (G, r)
	| dpts (IntSyn.Decl(G, IntSyn.LDec(NONE,A)),
		IntSyn.Decl(dPool, Used(r,_,_))) =
	  dpts (G, dPool) ^
	  "Clause (U) _^\t" ^
	  clauseToString (G, r)
    in
      dpts (G, dPool) ^
      "\t" ^
      (Int.toString st) ^ " strict and " ^
      (Int.toString lx) ^ " lax hypotheses\n\n"
    end
      

  fun linConToString (lCon, _, _) =                         (* Useless -ic *)
      let
	fun linConToString' (IntSyn.Null) = ""
	  | linConToString' (IntSyn.Decl (lCon, (UsedCon, _))) = 
	     linConToString' lCon
	  | linConToString' (IntSyn.Decl (lCon, (_, cid))) =
	     "\t" ^
	     Formatter.makestring_fmt(Print.formatEntry (IntSyn.sgnLookup cid))
	     ^ "\n" ^ (linConToString' lCon)
	val str = linConToString' lCon
      in
	case (String.compare (str, ""))
	  of EQUAL => ""
	   | _     => "Remaining linear assumptions:\n" ^ str
      end

end; (* functor CPrint *)
