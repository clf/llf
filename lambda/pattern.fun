(* Pattern Substitutions *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor Pattern (structure IntSyn' : INTSYN)
  : PATTERN
  (* :> PATTERN where IntSyn = IntSyn' *) = 
struct
  structure IntSyn = IntSyn'

  local 
    open IntSyn 

    exception NonContractible

    (* etaContract (U, s, n, fn (S',k) => S'') = k'

       Invariant: 
       if   G, V1, .., Vn |- s : G1  (.. linear or intuitionistic)
            and  G1 |- U : V
            and G, V1, .., Vn |- S''(Nil,1) : V' > V
       then if   lam V1...lam Vn. U[s] =eta*=> k 
	    then k' = k
            and  G |- k' : Pi V1...Pi Vn. V'
	    else NonContractible is raised
	      (even if U[s] might be eta-reducible to some other expressions).
    *)
    (* optimization(?): quick check w/o substitution first *)
    fun etaContract (r as Root (BVar(k), S), s, n, S') =
         (case bvarSub (k, s)
	    of Idx (k') =>
	        if k' > n
		  then (etaContract' (S, s, S'(Nil,1)); k'-n)
		  else raise NonContractible
             | _ => raise NonContractible)         (* Exp(U)  not treated *)
      | etaContract (Lam (Dec _, U), s, n, S') =
	 etaContract (U, dot1 s, n+1,
		      fn (S'',k) => S' (App (Root(BVar(k),Nil), S''), k+1))
      | etaContract (Lam (LDec _, U), s, n, S') =
	 etaContract (U, ldot1 s, n+1,
		      fn (S'',k) => S' (LApp (Root(BVar(k),Nil), S''), k+1))
      | etaContract (Pair (U1,U2), s, n, S') =
	 let
	   val k1 = etaContract (U1, s, n, fn (S'',k) => S' (Pi1 S'', k))
	   val k2 = etaContract (U2, s, n, fn (S'',k) => S' (Pi2 S'', k))
	 in
	   if k1 = k2
	     then k1
	     else raise NonContractible
	 end
      | etaContract (EClo (U, s'), s, n, S') =
	  etaContract (U, comp (s', s), n, S')
      | etaContract (EVar (ref (SOME(U)), _, _), s, n, S') =
	  etaContract (U, s, n, S')
      | etaContract _ = raise NonContractible
        (* Should fail: (c@S), (d@S), (F@S), X -- irrelevant for patterns *)
        (* Not treated (fails): <>, U@S *)
	(* Could weak head-normalize fo rmore thorough checks *)
        (* Impossible: L, Pi D.V *)

    (* etaContract' (S, s, S') = R'

       Invariant:
       If  G |- s : G1  and  G1 |- S : V > W  and G1 |- S' : V > W
       then if   S[s] =eta*=> S'[s]
	    then () 
       else NonContractible is raised
    *)
    and etaContract' (Nil, s, Nil) = ()
      | etaContract' (App (U, S), s, App (Root(BVar(k),Nil), S')) =
         let
	   val k' = etaContract (U, s, 0, fn (S'',k) => S'')
	 in
	   if k' = k
	     then etaContract' (S, s, S')
	     else raise NonContractible
	 end
      | etaContract' (LApp (U, S), s, LApp (Root(BVar(k),Nil), S')) =
         let
	   val k' = etaContract (U, s, 0, fn (S'',k) => S'')
	 in
	   if k' = k
	     then etaContract' (S, s, S')
	     else raise NonContractible
	 end
      | etaContract' (Pi1 S, s, Pi1 S') = etaContract' (S, s, S')
      | etaContract' (Pi2 S, s, Pi2 S') = etaContract' (S, s, S')
      | etaContract' _ = raise NonContractible (* should not arise *)


    (* dotEta (H, s) = s'
       
       Invariant: 
       If   G |- s : G1, V  and G |- H : V [s]
       then H  =eta*=>  H1
       and  s' = H1 . s
       and  G |- s' : G1, V
    *)
    fun dotEta (H as Idx _, s) = Dot (H, s)
      | dotEta (H as Exp (U, V), s) =
          let
	    val H' = Idx (etaContract (U, id, 0, fn (S'',k) => S''))
	             handle NonContractible => H
	  in
	    Dot (H', s)
	  end


    (* ldotEta (H, s) = s'
       
       Invariant: 
       If   G |- s : G1, V  and G |- H : V [s]
       then H  =eta*=>  H1
       and  s' = H1 .^ s
       and  G |- s' : G1, V
    *)
    fun ldotEta (H as Idx _, s) = LDot (H, s)
      | ldotEta (H as Exp (U, V), s) =
          let
	    val H' = Idx (etaContract (U, id, 0, fn (S'',k) => S''))
	             handle NonContractible => H
	  in
	    LDot (H', s)
	  end


    (* checkBvar (s,n) = B

       Invariant:
       If    G |- s : G' 
       and   s = n1 .. nm ^k  (.. can be linear)
       then  B iff  n <> ni for all 1 <= i <= m
               and  n < k
    *)
    fun checkBVar (Shift(k), n) = (n <= k)
      | checkBVar (Dot (Idx (n'), s), n) = 
         n <> n' andalso checkBVar (s, n)
      | checkBVar (LDot (Idx (n'), s), n) = 
	 n <> n' andalso checkBVar (s, n)
      | checkBVar _ = false

    (* checkSub s = B

       Invariant:
       If    G |- s : G' 
       and   s = n1 .. nm ^k  (.. can be linear)
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k for all 1 <= i <= m
    *)
    fun checkSub (Shift(k)) = true
      | checkSub (Dot (Idx (n), s)) = checkBVar (s, n) andalso checkSub s
(*    | checkSub (Dot (Exp (U), s)) cannot arise (?) *)
      | checkSub (LDot (Idx (n), s)) =  checkBVar (s, n) andalso checkSub s
(*    | checkSub (LDot (Exp (U), s)) cannot arise (?) *)
      | checkSub _ = false

  in
    val checkSub = checkSub
    val dotEta = dotEta
    val ldotEta = ldotEta
    val etaContract = (fn U => etaContract (U, id, 0, fn (S, k) => S))
  end (* local *)
end; (* functor Pattern *)
