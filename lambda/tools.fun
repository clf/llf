(* Debugging Tools *)
(* Author: Carsten Schuermann *)

functor Tools (structure IntSyn' : INTSYN
	       structure Normalize : NORMALIZE
		 sharing Normalize.IntSyn = IntSyn'
	       structure Whnf    : WHNF
	         sharing Whnf.IntSyn = IntSyn')
  : TOOLS
  (* :> TOOLS where IntSyn = IntSyn' *) =
struct
  structure IntSyn = IntSyn'

  local 
    open IntSyn

    fun whnfSub (s as Shift _) = s
      | whnfSub (Dot (H as Idx _, s)) =
	  Dot (H, whnfSub (s))
      | whnfSub (Dot (Exp (U,V), s)) =
	  Dot (Exp (whnfTerm (Whnf.whnf (U, id)), whnfTerm (Whnf.whnf (V,id))),
	       whnfSub(s))
      | whnfSub (LDot (H as Idx _, s)) =
	  LDot (H, whnfSub (s))
      | whnfSub (LDot (Exp (U,V), s)) =
	  LDot (Exp (whnfTerm (Whnf.whnf (U, id)),
		     whnfTerm (Whnf.whnf (V,id))),
	       whnfSub(s))

    and whnfTerm (U, s) = EClo (U, whnfSub s)

    val evarnames = Array.array (10000, (ref NONE) : Exp option ref)
    val evarnumber = ref 0

    fun name r = 
      let fun name' n =
	if n > !evarnumber then (Array.update (evarnames, n, r);
				 evarnumber := n;
				 n)
	else if Array.sub (evarnames, n) = r then n
	     else name' (n+1)
      in "E" ^ Int.toString(name' 0)
      end

    fun stringExp (Uni (Kind)) = "KIND"
      | stringExp (Uni (Type)) = "TYPE"
      | stringExp (Pi ((D, Maybe), U)) =
         "{" ^ stringDec (D) ^ "}" ^ stringExp (U)
      | stringExp (Pi ((D as Dec _, No), U)) =
	 "(" ^ stringDec (D) ^ ") -> (" ^ stringExp (U) ^ ")"
      | stringExp (Pi ((D as LDec _, No), U)) =
	 "(" ^ stringDec (D) ^ ") -o (" ^ stringExp (U) ^ ")"
      | stringExp (With (U', U'')) =
	 "(" ^ stringExp (U') ^ ") & (" ^ stringExp (U'') ^ ")"
      | stringExp (Top) = "<T>"
      | stringExp (Root (C, Nil)) = stringCon (C)
      | stringExp (Root (C, S)) = 
          "(" ^ stringCon (C) ^ " " ^ stringSpine (S) ^ ")"
      | stringExp (Lam (D, U)) =
	  "([" ^ stringDec (D) ^ "] " ^ stringExp (U) ^ ")"
      | stringExp (Pair (U', U'')) =
	  "<" ^ stringExp (U') ^ ", " ^ stringExp (U'') ^ ">"
      | stringExp (Unit) = "<>"
(*
      | stringExp (EClo (EVar (r as ref NONE, V, Constr), s)) = 
	  "(eclo " ^  name (r) ^ ":" ^ stringExp (V) ^ ")[" ^
	  stringSub (s) ^ "]" ^
          (if Constr = nil then "" else stringEqns Constr)
*)
      | stringExp (EClo (E as EVar _, s)) =
          "(eclo " ^ (stringExp E) ^ ")[" ^ stringSub (s) ^ "]" 
      | stringExp (EClo (E,s)) =
	  "(eclo: " ^ (stringExp E) ^ ", " ^ (stringSub s) ^ ")" 
      | stringExp (EVar (v,typ,C)) = (
          "(EVar = " ^ 
          (case !v of 
              SOME E => stringExp E
            | NONE => (name v) ^ "-No value") ^ ":" ^ (stringExp typ) ^
                      (if C = nil
			 then ""
		       else " plus Constraints "(*stringEqns C*) ) ^ ")") 
      | stringExp (Redex (E,S)) =
	  "(redex " ^ (stringExp E) ^ " " ^ (stringSpine S) ^ ")" 
    
    and stringEqns Eqs =
    let
      fun strngEqn nil = "" 
      |   strngEqn ((Eqn(E1,E2))::Rest) = " = " ^ (stringExp E2) ^ 
                                          " " ^ (strngEqn Rest)
    in
print "\nIn stringEqns...\n";
      "{--constraints " ^ (strngEqn Eqs) ^ "--}"
    end

    and stringCon (Const (c)) = 
          let fun stringExp' (ConstDec (n,_,_,_)) = n
		| stringExp' (LinDec   (n,_,_,_)) = n
	  in
	    stringExp' (sgnLookup (c))
	  end
      | stringCon (Defn (d)) = 
          let fun stringExp' (ConstDef (n,_,_,_,_)) =n
	  in
	    stringExp' (sgnLookup (d))
	  end
      | stringCon (BVar (k)) = Int.toString (k)
      | stringCon (FVar (n,V,s)) =
	  "(Fvar " ^ n ^ ":" ^ stringExp(V) ^ "<" ^ stringSub (s) ^ ">" ^ ")"
	  
    and stringSpine (Nil) = ""     (* something is fichy here *)
      | stringSpine (App (U, Nil)) = 
          stringExp (U) 
      | stringSpine (App (U, S)) = 
          " " ^ stringExp (U) ^ stringSpine S
      | stringSpine (LApp (U, S)) = 
          " ^ " ^ stringExp (U) ^ stringSpine S
      | stringSpine (Pi1 S) = 
          " Pi1 " ^ stringSpine (S) 
      | stringSpine (Pi2 S) = 
          " Pi2 " ^ stringSpine (S) 
      | stringSpine (SClo (S, s)) = 
          "|" ^ stringSpine  (S) ^ "[" ^ stringSub s ^"]|"
 
    and stringSub (Shift (0)) = "id"
      | stringSub (Shift (n)) = "|" ^ Int.toString (n)
      | stringSub (Dot (Idx (k), s)) = Int.toString (k) ^ "." ^ stringSub (s)
      | stringSub (Dot (Exp (U, _), s)) =
         "( " ^ stringExp(U) ^ ")." ^ stringSub (s)
      | stringSub (LDot (Idx (k), s)) = Int.toString (k) ^ ".^" ^ stringSub (s)
      | stringSub (LDot (Exp (U, _), s)) =
         "( " ^ stringExp(U) ^ ").^" ^ stringSub (s)

    and stringDec (Dec (NONE, V)) = "_:" ^ stringExp (V)
      | stringDec (Dec (SOME (n), V)) = n ^ ":" ^ stringExp (V)
      | stringDec (LDec (NONE, V)) = "_^" ^ stringExp (V)
      | stringDec (LDec (SOME (n), V)) = n ^ "^" ^ stringExp (V)

    fun stringEntry (ConstDec (n,i,exp,uni)) =
         "ConstDec ( " ^ n ^ ", " ^ (Int.toString i) ^ ", " ^
	 (stringExp exp) ^ ", " ^
	 (if uni = Kind then "Kind )" else "Type )")
      | stringEntry (ConstDef (n,i,exp1,exp2,uni)) =
	 "ConstDec ( " ^ n ^ ", " ^ (Int.toString i) ^ ", " ^
	 (stringExp exp1) ^ ", " ^ (stringExp exp2) ^ ", " ^
	 (if uni = Kind then "Kind )" else "Type )")
      | stringEntry (LinDec (n,i,exp,uni)) =
         "LinDec ( " ^ n ^ ", " ^ (Int.toString i) ^ ", " ^
	 (stringExp exp) ^ ", " ^
	 (if uni = Kind then "Kind )" else "Type )")

    fun stringEntries () = 
    let
      fun se 0 = ""
      |   se n = (se (n-1)) ^ "\n" ^ (stringEntry (IntSyn.sgnLookup (n-1)))
    in
      se (IntSyn.sgnSize())
    end

    fun stringCtx (Null) = "."
      | stringCtx (Decl (G, Dec (xOpt, V))) = 
          (stringCtx G) ^ ",\n  " ^
	  (stringDec (Dec (xOpt, Normalize.normalize (V, id))))
      | stringCtx (Decl (G, LDec (xOpt, V))) = 
          (stringCtx G) ^ ",^\n  " ^
	  (stringDec (Dec (xOpt, Normalize.normalize (V, id))))

	    

    val a = Array.array (10000, (ref NONE) : Exp option ref);
    val evars = ref 0;

  in
(*     val stringExp = fn U => stringExp (Normalize.normalize (U, IntSyn'.id))  *)
     val stringExp = stringExp
    val stringSub = stringSub
    val stringCtx = stringCtx
    val stringEntry = stringEntry 
    val stringEntries = stringEntries 
    val stringSpine = stringSpine
    val stringDec = stringDec
    val name = name
    val normalizeExp = Normalize.normalize
  end  (* local *)
end;  (* functor Tools *)
