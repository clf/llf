(* Twelf             Copyright (c) 1997 by Carnegie Mellon University *)
(* Author: Frank Pfenning      <fp+@cs.cmu.edu>                       *)
(*         Carsten Schuermann  <carsten+@cs.cmu.edu>                  *)
(*         Iliano Cervesato    <iliano@cs.stanford.edu>               *)

(* Linearity check                                                    *)

functor LinCheck (structure IntSyn' : INTSYN
		  structure Whnf    : WHNF
		    sharing Whnf.IntSyn = IntSyn'
		  structure Paths  : PATHS)
  : LINCHECK
  (* :> sig include LINCHECK sharing IntSyn = IntSyn' end *) = 
struct
  structure IntSyn = IntSyn'
  structure Paths = Paths
  structure IPrint = IPrint

  exception Error of string
  exception Warning of string

  datatype linCtx =                (* Auxiliary linear context        *)
    Nll                            (* H ::= .                         *)
  | Int of linCtx                  (*     | H, x                      *)
  | Lin of linCtx                  (*     | H,^ x                     *)
  | Con of linCtx                  (*     | H,^ _                     *)
                                   (* "?" will stand for "," or ",^"  *)

  type rightLinCtx = linCtx * int  (* Hk ::= (H, k)                   *)
                                   (* Invariant: k <= |H|             *)
                                   (* H = x1?...?xn?y1?...?yk         *)
                                   (* linear variables among x1...xn  *)
                                   (* are unavailable for consumption *)

  datatype slack =                 (* Slack indicator / T-flag        *)
    Slack
  | NoSlack

  (* Given Hk = (H, k) with H = (x1?...?xn?y1?...?yk),  y1?...?yk is  *)
  (* denoted H_k and x1?...?xn is denoted H\k                         *)

  (* We say that H parallels G, written H // G if                     *)
  (* - H and G have the same length                                   *)
  (* - every occurrence of Int in H corresponds to an occurrence of   *)
  (*   Dec in G                                                       *)
  (* - every occurrence of Lin or Con in H corresponds to an          *)
  (*   occurrence of LDec in G.                                       *)

  (* We write  (H,k) |-o U / (H',t)  if                               *)
  (* - there is a context G such that H // G and an expression V such *)
  (*   that G |- U : V                                                *)
  (* - H' differs from H only by the replacement of zero or more      *)
  (*   linear assumption with _ among its rightmost k variables,      *)
  (* - each of the replaced variable occurs linearly in U,            *)
  (* - t is Slack if Unit occurs relevantly in U, NoSlack otherwise.  *)

  (* (H,k) |-o S / (H',t)  is defined similarly.                      *)

  (* We write  |H|  for the length of H, defined as the number of Int *)
  (* Lin and Con it contains.                                         *)


  (* eqLinCtx (H, H', k) = B

     Invariant:
     If    |H| = |H'| <= k
     and   H\k = H'\k
     then  B iff  H_k = H'_k

     Note: the non lin-active part of H and H2 are identical
  *)
  fun eqLinCtx (_, _, 0) = true
    | eqLinCtx (Int H, Int H', k) = eqLinCtx (H, H', k-1)
    | eqLinCtx (Lin H, Lin H', k) = eqLinCtx (H, H', k-1)
    | eqLinCtx (Con H, Con H', k) = eqLinCtx (H, H', k-1)
    | eqLinCtx _ = false


  (* subLinCtx (H, H', k) = B

     Invariant:
     If    |H| = |H'| <= k
     and   H\k = H'\k
     then  B iff  H_k = H'_k, except that some occurrence of
           Lin in H' can be replaced by Con in H
  *)
  fun subLinCtx (_, _, 0) = true
    | subLinCtx (Int H, Int H', k) = subLinCtx (H, H', k-1)
    | subLinCtx (Lin H, Lin H', k) = subLinCtx (H, H', k-1)
    | subLinCtx (Con H, Con H', k) = subLinCtx (H, H', k-1)
    | subLinCtx (Con H, Lin H', k) = subLinCtx (H, H', k-1)
    | subLinCtx _ = false


  (* intersect (H, H', k) = H''

     Invariant:
     If    |H| = |H'| <= k
     and   H\k = H'\k
     and   H_k and H'_k have matching occurrences of Int
     then  |H''| = |H|
     and   H''\k = H\k
     and   H''_k contains Int whenever H_k contains Int,
                 contains Lin whenever both H_k and H'_k contain Lin
		 contains Con whenever either H_k or H'_k contain Con
           in the corresponding place
  *)
  fun intersect (H, _, 0) = H
    | intersect (Int H, Int H', k) = Int (intersect (H, H', k-1))
    | intersect (Lin H, Lin H', k) = Lin (intersect (H, H', k-1))
    | intersect (Lin H, Con H', k) = Con (intersect (H, H', k-1))
    | intersect (Con H, Lin H', k) = Con (intersect (H, H', k-1))
    | intersect (Con H, Con H', k) = Con (intersect (H, H', k-1))
    (* No other case can arise *)

  (* intCtx (H, k) = B

     Invariant:
     If    |H| <= k
     then  B iff H_k does not contain any Lin
  *)
  fun intCtx (_, 0) = true
    | intCtx (Int H, k) = intCtx (H, k-1)
    | intCtx (Con H, k) = intCtx (H, k-1)
    | intCtx _ = false   (* Lin H *)

  (* Checking linearity requires adopting a context management policy.
     Here, we adopted RM_2 (see ELP'96), i.e. we have input/output
     contexts and a slack indicator, but no sophisticate treatment of &.
     Little damage seems to derive from not recognizing linearity
     violations as early as possible, while it saves continuously
     reshuffling the context.  Moreover, since no search is involved,
     no completeness is lost.
  *)

  local
    structure I = IntSyn
    structure P = Paths

    exception Error' of P.occ * string
    exception Warning' of P.occ * string


    (* intVar (H, k') = B

       Invariant:
       If     k' <= |H|
       then   B iff the k'-th topmost item of H is Int
    *)
    fun intVar (Int _, 1) = true
      | intVar (Lin _, 1) = false
      | intVar (Con _, 1) = false
      | intVar (Int H, k') = intVar (H, k'-1)
      | intVar (Lin H, k') = intVar (H, k'-1)
      | intVar (Con H, k') = intVar (H, k'-1)


    (* linVar (H, k, k', occ) = H'
     
       Invariant:
       If     k' <= |H|
       then   If the k'-th topmost item of H is Int
                then H'=H
	      If k' <= k and the k'-th topmost item of H is Lin
		then H' differs from H by the replacement of that item with Con
              Otherwise, Error' (occ, <msg>) is raised
    *)
    fun linVar (H, 0, k', occ) =
         if intVar (H, k')
	   then H
	 else raise Error' (occ, "intuitionistic application")
      | linVar (H as Int H', _, 1, _) = H
      | linVar (Lin H', _, 1, _) = Con H'
      | linVar (Con H', _, 1, occ) = raise Error' (occ, "contraction")
      | linVar (Int H', k, k', occ) = Int (linVar (H', k-1, k'-1, occ))
      | linVar (Lin H', k, k', occ) = Lin (linVar (H', k-1, k'-1, occ))
      | linVar (Con H', k, k', occ) = Con (linVar (H', k-1, k'-1, occ))


    (* linExpW ((H, k), (U, s), occ) = (H', t)

       Invariant:
       If    G |- s : G1    G1 |- U : V      (U,s) in whnf
       and   H // G
       and   occ is an occurrence tree for U
       then  (H,k) |-o U[s] / (H',t)
       and   |H'| = |H|     H\k = H'\k

       Raises Error' (occ', <msg>) if U[s] is not linear w.r.t. H, where occ'
       is some extension of occ
       Raises Warning' (occ', <msg>) if U[s] contains EVars which have
       instances that might violate linearity
    *)
    fun linExpW ((H,_), (I.Uni _, _), _) = (H, NoSlack)
      | linExpW (Hk as (H,_), (I.Pi (DP as (I.Dec _,_), V), s), occ) =
	 let
	     val (H',_) = linDecP (Hk, (DP, s), P.label occ)
	     val (Int H'',_) = linExp ((Int H', 0), (V, I.dot1 s), P.body occ)
	 in
	     (H'', NoSlack)
	 end
      | linExpW (Hk as (H,_), (I.Pi (DP as (I.LDec _,_), V), s), occ) =
	 let
	     val (H',_) = linDecP (Hk, (DP, s), P.label occ)
	     val (Con H'',_) = linExp ((Con H', 0), (V, I.ldot1 s), P.body occ)
	         (* Using Con, Lin or even Int does not matter *)
	 in
	     (H'', NoSlack)
	 end
      | linExpW (Hk as (H,_), (I.With (V', V''), s), occ) =
	 let
	     val (H',_) = linExp (Hk, (V', s), P.pair1 occ)
	     val (H'',_) = linExp (Hk, (V'', s), P.pair2 occ)
	 in
	     (H'', NoSlack)
	 end
      | linExpW ((H,_), (I.Top, _), _) = (H, NoSlack)

      | linExpW (Hk as (H,k), (I.Root (C, S), s), occ) =
	 let
	   val H' = linCon (Hk, C, P.head occ)         (* -ic ? *)
	 in
	   linSpine ((H',k), (S, s), (1, occ))
	 end

      | linExpW ((H,k), (I.Lam (D as I.Dec _, U), s), occ) =
	 let
	     val (H',_) = linDec ((H,0), (D, s), P.label occ)
	     val (Int H'',t) = linExp ((Int H', k+1), (U, I.dot1 s),
				       P.body occ)
	 in
	     (H'', t)
	 end
      | linExpW ((H,k), (I.Lam (D as I.LDec _, U), s), occ) =
	 let
	     val (H',_) = linDec ((H,0), (D, s), P.label occ)
	     val Ht = linExp ((Lin H', k+1), (U, I.ldot1 s), P.body occ)
	 in
	     (case Ht
		of (Con H'', t) => (H'', t)
		 | (Lin H'', Slack) => (H'', Slack)
		 | (Lin _, NoSlack) =>
		    raise Error' (occ, "linear abstraction"))
	         (* No other case can arise *)
	 end
      | linExpW (Hk as (H,k), (I.Pair (U', U''), s), occ) =
	 let
	     val (H',t') = linExp (Hk, (U', s), P.pair1 occ)
	     val (H'',t'') = linExp (Hk, (U'', s), P.pair2 occ)
	 in
	     (case (t',t'')
		of (NoSlack, NoSlack) =>
		     if eqLinCtx (H', H'', k)
		       then (H', NoSlack)
		       else raise Error' (occ, "conjuncts use different linear assumptions")
		 | (NoSlack, Slack) =>
		     if subLinCtx (H', H'', k)
		       then (H', NoSlack)
		       else raise Error' (occ, "left conjunct uses too many linear assumptions")
		 | (Slack, NoSlack) =>
		     if subLinCtx (H'', H', k)
		       then (H'', NoSlack)
		       else raise Error' (occ, "right conjunct uses too many linear assumptions")
		 | (Slack, Slack) => (intersect (H', H'', k), Slack))
	 end
      | linExpW ((H,_), (I.Unit, _), _) = (H, Slack)

      | linExpW (Hk, (I.EVar _, s), occ) = 
	 (linSub (Hk, s)
	  handle Error' (_, msg) => raise Warning' (occ, msg)
	       | Warning' (_, msg) => raise Warning' (occ, msg))
        (* No cases for EClo and Redex *)

    (* linExp ((H, k), (U, s), occ) = (H', t)
       Same as linExpW, but (U,s) needs not to be in whnf
    *)
    and linExp (Hk, Us as (UU,_), occ) = linExpW (Hk, Whnf.whnf Us, occ)

    (* linCon ((H, k), C, occ) = H'

       Invariant:
       If    G |- Root (C, S) : V
       and   C is either a bound variable, a constant or a definition label
       and   occ is an occurrence tree for Root (C, S)
       and   H // G
       and   all definitions have been lin-checked in the empty context
       then if C is a constant, a definition or an intuitionistic
               bound variable,
            then H' = H;
	    if C is a linear bound variable declared in H_k,
	    then H' differs from H only by the replacemente of the Lin
	         marker for C with Con
	    otherwise Error' (occ, <msg>) is raised

       Raises Error' (occ, <msg>) if U[s] is not linear w.r.t. H
    *)
    and linCon ((H, k) , I.BVar k', occ) = linVar (H, k, k', occ)
      | linCon ((H,_), I.Const cid, occ) = 
         (case I.sgnLookup cid
	    of I.ConstDec _ => H
             | I.ConstDef _ => H
             | I.LinDec _   =>
	        raise Error' (occ, "linear constants can appear only in proof-terms"))
      | linCon ((H,_), I.Defn _, _) = H	(* Definitions are intuitionistic *)
					(* and previously lin-checked     *)
      (* No case for FVars *)


    (* linSpine ((H, k), (S, s), (p, occ)) = (H', t)

       Invariant:
       If    G |- s : G1    G1 |- Root (C, S') : V'
       and   occ is an occurrence tree for Root (C, S')
       and   S' = S'' @ S  and  S'' contains p-1 applications
       and   G1 |- S : V > V'
       and   H // G
       then  (H,k) |-o S[s] / (H',t)
       and   |H'| = |H|     H\k = H'\k

       Raises Error' (occ', <msg>) if S[s] is not linear w.r.t. H, for some
       extension occ' of occ
       Raises Warning' (occ', <msg>) if U[s] contains EVars which have
       instances that might violate linearity
    *)
    and linSpine ((H,_), (I.Nil, _), _) = (H, NoSlack)
      | linSpine ((H, k), (I.App (U, S), s), po as (p, occ)) =
         let
	   val (H', _)  = linExp ((H,0), (U,s), P.arg po)
	 in
	   linSpine ((H', k), (S, s), (p+1, occ))
	 end
      | linSpine (Hk as (H, k), (I.LApp (U, S), s), po as (p, occ)) =
         let
	   val (H', t')  = linExp (Hk, (U, s), P.arg po)
	   val (H'',t'') = linSpine ((H', k), (S, s), (p+1, occ))
	 in
	   (case (t', t'')
	      of (NoSlack, NoSlack) => (H'', NoSlack)
	      | _ => (H'', Slack))
	 end
      | linSpine (Hk, (I.Pi1 S, s), po) = linSpine (Hk, (S, s), po)
      | linSpine (Hk, (I.Pi2 S, s), po) = linSpine (Hk, (S, s), po)
      | linSpine (Hk, (I.SClo (S, s'), s), po) =
	 linSpine (Hk, (S, I.comp (s', s)), po)


    (* linDec ((H, k), (x:V, s), occ) = (H', t)

       Invariant:
       If    G |- s : G1    G1 |- V : L
       and   occ is an occurrent tree for x:V
       and   H // G
       then  (H,k) |-o V[s] / (H',t)
       and   |H'| = |H|     H\k = H'\k

       Raises Error' (occ', <msg>) if V[s] is not linear w.r.t. H, for some
       extension occ' of occ
       Raises Warning' (occ', <msg>) if U[s] contains EVars which have
       instances that might violate linearity

       Note: always called with k=0
    *)
    and linDec (Hk, (I.Dec (_,V), s), occ) = linExp (Hk, (V, s), occ)
      | linDec (Hk, (I.LDec (_,V), s), occ) = linExp (Hk, (V, s), occ)

    (* linDecP see linDec *)
    and linDecP (Hk, ((D, _), s), occ) = linDec (Hk, (D, s), occ)

    (* linSub ((H, k), s) = (H', t)

       Invariant:
       If    G |- s : G'
       and   H // G
       then  (H,k) |-o s / (H',t)
       and   |H'| = |H|     H\k = H'\k

       Raises Error' (occ, msg) if V[s] is not linear w.r.t. H
       Raises Warning' (occ, msg) if s contains free linear variables
    *)
    and linSub ((H,_), I.Shift(n)) = (H, NoSlack)            (* ? -ic *)
      | linSub ((H,k), I.Dot(I.Idx k', s)) =
	 let
	   fun linVar' (H, 0, k') =
	        if intVar (H, k')
		  then H
		else
		  raise Warning' (P.top, "linear instances should be considered")
	     | linVar' (H as Int H', _, 1) = H
	     | linVar' (Lin H', _, 1) =
		raise Warning' (P.top, "linear instances should be considered")
	     | linVar' (Con H', _, 1) =
		raise Warning' (P.top, "linear instances should be considered")
	     | linVar' (Int H', k, k') = Int (linVar' (H', k-1, k'-1))
	     | linVar' (Lin H', k, k') = Lin (linVar' (H', k-1, k'-1))
	     | linVar' (Con H', k, k') = Con (linVar' (H', k-1, k'-1))
	   val H' = linVar' (H, k, k')
	 in
	   linSub ((H',k), s)
	 end
      | linSub ((H,k), I.Dot(I.Exp (U,_), s)) =
	 let
	   val (H', _) = linExp ((H,0), (U,I.id), P.top)             (* H'=H *)
	 in
	   linSub ((H',k), s)
	 end
      | linSub ((H,k), I.LDot(I.Idx k', s)) =
	 let
	   val H' = linVar (H, k, k', P.top)
	 in
	   linSub ((H',k), s)
	 end
      | linSub (Hk as (H,k), I.LDot(I.Exp (U,_), s)) =
	 let
	   val (H', t') = linExp (Hk, (U, I.id), P.top)           (* H'=H *)
	   val (H'',t'') = linSub ((H',k), s)
	 in
	   (case (t', t'')
	      of (NoSlack, NoSlack) => (H'', NoSlack)
	      | _ => (H'', Slack))
	 end


    fun error (r, msg) =
         raise Error ((P.toString r) ^ " Linearity violation (" ^ msg ^ ")")

    fun warning (r, msg) =
         raise Warning ((P.toString r) ^ " " ^ msg)

    fun linCheckInit U = linExp ((Nll, 0), (U, IntSyn.id), P.top)
  in
    (* linCheck U = ()

       Invariant:
       If    . |- U : V
       then  (.,.) |-o U / (.,t)

       Raises Error <msg> if U is not linear
    *)
    fun linCheck (U, ocOpt) =
         ((linCheckInit U
	   handle Error' (occ, msg) =>
	           (case ocOpt
		      of NONE => raise Error ("Linearity violation (" ^ msg ^ ")")
		       | SOME occTree =>
			  error (P.occToRegionExp occTree occ, msg))
		| Warning' (occ, msg) =>
	           (case ocOpt
		      of NONE => raise Warning msg
		       | SOME occTree =>
			  warning (P.occToRegionExp occTree occ, msg)));
	  ())

    fun linCheckEntry (IntSyn.ConstDec (_, _, V, L), occTree) =
         ((linCheckInit V
	   handle Error' (occ, msg) =>
			  error (P.occToRegionDecl occTree occ, msg)) ;
	          (* Warning' cannot be raised *)
	  ())
      | linCheckEntry (IntSyn.ConstDef (_, _, U, V, L), occTree) =
         ((linCheckInit U
	   handle Error' (occ, msg) =>
			  error (P.occToRegionDefn1 occTree occ, msg)) ;
	          (* Warning' cannot be raised *)
	  (linCheckInit V
	   handle Error' (occ, msg) =>
			  error (P.occToRegionDefn2 occTree occ, msg)) ;
	          (* Warning' cannot be raised *)
	  ())
      | linCheckEntry (IntSyn.LinDec (_, _, V, L), occTree) =
         ((linCheckInit V
	   handle Error' (occ, msg) =>
			  error (P.occToRegionDecl occTree occ, msg)) ;
	          (* Warning' cannot be raised *)
	  ())

    fun linCheckQuery (U, occ) = linCheck (U, SOME(occ))
  end
end;  (* functor LinCheck *)
