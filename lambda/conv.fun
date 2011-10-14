(* Convertibility Modulo Beta and Eta *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor Conv
  (structure IntSyn' : INTSYN
   structure Whnf   : WHNF
   sharing Whnf.IntSyn = IntSyn')
     : CONV
  (* :> CONV where IntSyn = IntSyn' *) =
struct
  structure IntSyn = IntSyn'

  local
    open IntSyn
      
    (* eqUni (L1, L2) = B iff L1 = L2 *)
    fun eqUni (Type, Type) = true
      | eqUni (Kind, Kind) = true
      | eqUni _ = false
      
    (* convExpW ((U1, s1), (U2, s2)) = B

       Invariant: 
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1) in whnf
            G |- s2 : G2    G2 |- U2 : V2    (U2,s2) in whnf
            G |- V1[s1] == V2[s2] == V : L
       then B iff G |- U1[s1] = U2[s2] : V

       Effects: EVars may be lowered
    *)
    fun convExpW ((Uni(L1), _), (Uni(L2), _)) =
          eqUni (L1, L2)

      | convExpW (Us1 as (Root (C1, S1), s1), Us2 as (Root(C2, S2), s2)) =
	  (* s1 = s2 = id by whnf invariant *)
          (* order of calls critical to establish convSpine invariant *)
          (case (C1, C2) of 
	     (BVar(k1), BVar(k2)) => 
	       (k1 = k2) andalso convSpine ((S1, s1), (S2, s2))
	   | (Const(c1), Const(c2)) => 	  
	       (c1 = c2) andalso convSpine ((S1, s1), (S2, s2))
	   | (FVar (n1,_,s1'), FVar (n2,_,s2')) =>
  	       (* s1' = s2' = ^|G| *)
	       (n1 = n2) andalso convSpine ((S1, s1), (S2, s2))
	   | (Defn (d1), Defn (d2)) =>
	       (* because of strictness *) 
	       ((d1 = d2) andalso convSpine ((S1, s1), (S2, s2)))
	       orelse convExpW (Whnf.expandDefn (Us1), Whnf.expandDefn (Us2))
	   | (Defn (d1), _) => convExpW (Whnf.expandDefn Us1, Us2)
	   | (_, Defn(d2)) => convExpW (Us1, Whnf.expandDefn Us2)
	   | _ => false)

      | convExpW ((Pi (DP1 as (Dec _, _), V1), s1),
		  (Pi (DP2 as (Dec _, _), V2), s2)) =
	  convDecP ((DP1, s1), (DP2, s2)) 
	  andalso convExp ((V1, dot1 s1), (V2, dot1 s2))

      | convExpW ((Pi (DP1 as (LDec _, _), V1), s1),
		  (Pi (DP2 as (LDec _, _), V2), s2)) =
	  convDecP ((DP1, s1), (DP2, s2)) 
	  andalso convExp ((V1, ldot1 s1), (V2, ldot1 s2))

      | convExpW ((With (V1', V1''), s1), (With (V2', V2''), s2)) =
	  convExp ((V1', s1), (V2', s2)) andalso
	  convExp ((V1'', s1), (V2'', s2))

      | convExpW ((Top, _), (Top, _)) = true

      | convExpW ((Lam (D1 as Dec _, U1), s1), (Lam (D2 as Dec _, U2), s2)) =
	(* G |- D1[s1] = D2[s2] by typing invariant *)
	  convExp ((U1, dot1 s1),  (U2, dot1 s2))

      | convExpW ((Lam (D1 as Dec _, U1), s1), (U2, s2)) =
	  convExp ((U1, dot1 s1),
		   (Redex (EClo (U2, shift), 
			   App (Root (BVar (1), Nil), Nil)), dot1 s2)) 

      | convExpW ((U1,s1), (Lam(D2 as Dec _, U2) ,s2)) =
	  convExp ((Redex (EClo (U1, shift), 
			   App (Root (BVar (1), Nil), Nil)), dot1 s1),
		   (U2, dot1 s2))

      | convExpW ((Lam (D1 as LDec _, U1), s1), (Lam (D2 as LDec _, U2), s2)) =
	(* G |- D1[s1] = D2[s2] by typing invariant *)
	  convExp ((U1, ldot1 s1),  (U2, ldot1 s2))

      | convExpW ((Lam (D1 as LDec _, U1), s1), (U2, s2)) =
	  convExp ((U1, ldot1 s1),
		   (Redex (EClo (U2, shift), 
			   LApp (Root (BVar (1), Nil), Nil)), ldot1 s2)) 

      | convExpW ((U1,s1), (Lam(D2 as LDec _, U2) ,s2)) =
	  convExp ((Redex (EClo (U1, shift), 
			   LApp (Root (BVar (1), Nil), Nil)), ldot1 s1),
		   (U2, ldot1 s2))

      | convExpW ((Pair (U1', U1''), s1), (Pair (U2', U2''), s2)) =
	  convExp ((U1', s1),  (U2', s2)) andalso
	  convExp ((U1'', s1),  (U2'', s2))

      | convExpW ((Pair (U1', U1''), s1), (U2, s2)) =
	  convExp ((U1', s1), (Redex (U2, Pi1 Nil), s2)) andalso
	  convExp ((U1'', s1), (Redex (U2, Pi2 Nil), s2))

      | convExpW ((U1,s1), (Pair (U2', U2'') ,s2)) =                           
	  convExp ((Redex (U1, Pi1 Nil), s1), (U2', s2)) andalso
	  convExp ((Redex (U1, Pi2 Nil), s1), (U2'', s2))

      | convExpW ((Unit, _), (Unit, _)) = true
	  (* ETA: unexpanded terms of unit type are not considered *)

      | convExpW ((EVar (r1, _, _), s1), (EVar(r2, _, _), s2)) = 
	  (r1 = r2) andalso convSub (s1, s2)

      | convExpW _ = false
        (* Possible are:
           L <> Pi D. V   Pi D. V <> L
           X <> U         U <> X
	   and many more.
	*)

    (* convExp ((U1, s1), (U2, s2)) = B
     
       Invariant: 
       as above, but (U1, s1), (U2, s2) need not to be in whnf
       Effects: EVars may be lowered
    *)
    and convExp (Us1, Us2) = convExpW (Whnf.whnf Us1, Whnf.whnf Us2)

    (* convSpine ((S1, s1), (S2, s2)) = B
     
       Invariant: 
       If   G |- s1 : G1     G1 |- S1 : V1 > W1
            G |- s2 : G2    G2 |- S2 : V2 > W2
            G |- V1[s1] = V2[s2] = V : L
            G |- W1[s1] = W2[s2] = W : L
       then B iff G |- S1 [s1] = S2 [s2] : V > W

       Effects: EVars may be lowered
    *)
    and convSpine ((Nil, _), (Nil, _)) = true
      | convSpine ((App (U1, S1), s1), (App (U2, S2), s2)) = 
          convExp ((U1, s1), (U2, s2)) andalso convSpine ((S1, s1), (S2, s2))
      | convSpine ((LApp (U1, S1), s1), (LApp (U2, S2), s2)) = 
          convExp ((U1, s1), (U2, s2)) andalso convSpine ((S1, s1), (S2, s2))
      | convSpine ((Pi1 S1, s1), (Pi1 S2, s2)) = 
          convSpine ((S1, s1), (S2, s2))
      | convSpine ((Pi2 S1, s1), (Pi2 S2, s2)) = 
          convSpine ((S1, s1), (S2, s2))
      | convSpine ((SClo (S1, s1'), s1), Ss2) = 
	  convSpine ((S1, comp (s1', s1)), Ss2)
      | convSpine (Ss1, (SClo (S2, s2'), s2)) = 
	  convSpine (Ss1, (S2, comp (s2', s2)))
    (* no others are possible due to typing invariants *)

    (* convSub (s1, s2) = B

     Invariant:
     If  G |- s1 : G'
         G |- s2 : G'
     then B iff G |- s1 = s2 : G'
     Effects: EVars may be lowered
    *)
    and convSub (Shift(n), Shift(m)) = true (* n = m by invariants *)
      | convSub (Shift(n), s2 as Dot _) = 
          convSub (Dot(Idx(n+1), Shift(n+1)), s2)
      | convSub (s1 as Dot _, Shift(m)) = 
	  convSub (s1, Dot(Idx(m+1), Shift(m+1)))
      (* convSub (Shift _, LDot _)  cannot arise -ic *)
      (* convSub (LDot _, Shift _)  cannot arise -ic *)
      | convSub (Dot(H1,s1), Dot(H2,s2)) =
	  (case (H1, H2)
	     of (Idx (n1), Idx (n2)) => (n1 = n2)
              | (Exp (U1, _), Exp (U2, _)) => convExp ((U1, id), (U2, id))
	      | (Exp (U1, _), Idx (n2)) =>
	          convExp ((U1, id), (Root(BVar(n2), Nil), id))
	      | (Idx (n1), Exp (U2, _)) =>
		  convExp ((Root(BVar(n1), Nil), id), (U2, id)))
	  andalso convSub (s1, s2)
      | convSub (LDot(H1,s1), LDot(H2,s2)) =
	  (case (H1, H2)
	     of (Idx (n1), Idx (n2)) => (n1 = n2)
              | (Exp (U1, _), Exp (U2, _)) => convExp ((U1, id), (U2, id))
	      | (Exp (U1, _), Idx (n2)) =>
	          convExp ((U1, id), (Root(BVar(n2), Nil), id))
	      | (Idx (n1), Exp (U2, _)) =>
		  convExp ((Root(BVar(n1), Nil), id), (U2, id)))
	  andalso convSub (s1, s2)
      (* convSub (Dot _, LDot _)  cannot arise -ic *)
      (* convSub (LDot _, Dot _)  cannot arise -ic *)

    (* convDec ((x1:V1, s1), (x2:V2, s2)) = B
       
       Invariant: 
       If   G |- s1 : G'     G'  |- V1 : L
            G |- s2 : G''    G'' |- V2 : L 
       then B iff G |- V1 [s1]  = V2 [s2] : L
       Effects: EVars may be lowered
    *)
    and convDec ((Dec (_, V1), s1), (Dec (_, V2), s2)) =
         convExp ((V1, s1), (V2, s2))
      | convDec ((LDec (_, V1), s1), (LDec (_, V2), s2)) =
         convExp ((V1, s1), (V2, s2))

    (* convDecP see convDec *)
    and convDecP (((D1, P1), s1), ((D2, P2), s2)) =
         convDec ((D1, s1), (D2, s2))
      
  in
    val conv = convExp 
    val convDec = convDec
  end (* local *)
end;  (* functor Conv *)
