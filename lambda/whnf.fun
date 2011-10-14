(* Weak Head-Normal Forms *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor Whnf (structure IntSyn' : INTSYN
	      structure Pattern : PATTERN
	      sharing Pattern.IntSyn = IntSyn')
  : WHNF
  (* :> WHNF where IntSyn = IntSyn' *) =
struct
  structure IntSyn = IntSyn'

  local 
    open IntSyn

    (* appendSpine ((S1, s1), (S2, s2)) = S' 

       Invariant:
       If    G |- s1 : G1   G1 |- S1 : V1' > V1 
       and   G |- s2 : G2   G2 |- S2 : V2  > V2'
       and   G |- V1 [s1] == V2 [s2]
       then  G |- S' : V1' [s1] > V2' [s2]   
    *)
    fun appendSpine ((Nil, s1), Ss2) = SClo Ss2
      | appendSpine ((App (U1, S1), s1), Ss2) =
          App (EClo (U1, s1), appendSpine ((S1, s1), Ss2))
      | appendSpine ((LApp (U1, S1), s1), Ss2) =
          LApp (EClo (U1, s1), appendSpine ((S1, s1), Ss2))
      | appendSpine ((Pi1 S1, s1), Ss2) =
          Pi1 (appendSpine ((S1, s1), Ss2))
      | appendSpine ((Pi2 S1, s1), Ss2) =
          Pi2 (appendSpine ((S1, s1), Ss2))
      | appendSpine ((SClo (S1, s1'), s1), Ss2) =
	  appendSpine ((S1, comp(s1', s1)), Ss2)

    (* whnfRedex ((U, s1), (S, s2)) = (U', s')

       Invariant:
       If    G |- s1 : G1   G1 |- U : V1,   (U,s1) whnf 
	     G |- s2 : G2   G2 |- S : V2 > W2
	     G |- V1 [s1] == V2 [s2] == V : L
       then  G |- s' : G',  G' |- U' : W'
       and   G |- W'[s'] == W2[s2] == W : L
       and   G |- U'[s'] == (U[s1] @ S[s2]) : W
       and   (U',s') whnf

       Effects: EVars may be lowered to base type.
    *)
    fun whnfRedex (Us, (SClo (S, s2'), s2)) =
          whnfRedex (Us, (S, comp (s2', s2)))
      | whnfRedex (Us as (Root R, s1), (Nil, s2)) = Us
      | whnfRedex ((Root (C1, S1), s1), (S2, s2)) =
	  (* S2 <> Nil, only possible if term is not eta-expanded *)
	  (Root (C1, appendSpine ((S1, s1), (S2, s2))), id)
      | whnfRedex ((Lam (Dec(_,V2), U1), s1), (App (U2, S), s2)) =
	  whnfRedex (whnf (U1, Pattern.dotEta
			   (headSub (Exp (U2, V2), s2), s1)), (S, s2)) 
	  (* whnfRedex (whnf (U1, Dot (headSub (Exp (U2, V2), s2), s1)), (S, s2)) *)
      | whnfRedex ((Lam (LDec(_,V2), U1), s1), (LApp (U2, S), s2)) =
	  whnfRedex (whnf (U1, Pattern.ldotEta
			   (headSub (Exp (U2, V2), s2), s1)), (S, s2)) 
	  (* whnfRedex (whnf (U1, LDot (headSub (Exp (U2, V2), s2), s1)), (S, s2)) *)
      | whnfRedex ((Pair (U1, U1'), s1), (Pi1 (S), s2)) =
	  whnfRedex ((U1, s1), (S, s2))
      | whnfRedex ((Pair (U1, U1'), s1), (Pi2 (S), s2)) =
	  whnfRedex ((U1', s1), (S, s2))
      | whnfRedex (Us as (Lam _, s1), _) = Us  (* S2[s2] = Nil *)
      | whnfRedex (Us as (Pair _, s1), _) = Us  (* S2[s2] = Nil *)
      | whnfRedex (Us as (Unit, s1), _) = Us
      | whnfRedex (Us as (EVar _, s1), (Nil, s2)) = Us  (* pb with <T> -ic! *)
      | whnfRedex (Us as (X as EVar _, s1), Ss2) = 
	  (* Ss2 must be <> Nil, since prior cases do not apply *)
	  (* lower X results in redex, optimize by unfolding call to whnfRedex *)
	  (lower X; whnfRedex (whnf Us, Ss2))
      (* Uni and Pi can arise after instantiation of EVar X : K *)
      | whnfRedex (Us as (Uni _, s1), _) = Us	(* S2[s2] = Nil *)
      | whnfRedex (Us as (Pi _, s1), _) = Us	(* S2[s2] = Nil *)
      | whnfRedex (Us as (With _, s1), _) = Us	(* S2[s2] = Nil *)
      | whnfRedex (Us as (Top, s1), _) = Us	(* S2[s2] = Nil *)
      (* Other cases impossible since (U,s1) whnf *)

    (* lower (X) = (), effect instantiates X

       Invariant:
       If    G |- X : (Pi x:V''.V'),
       then  X := Lam x:V''. X'  where  G, x:V'' |- X' : V'
       If    G |- X : (LPi x:V''.V'),
       then  X := LLam x:V''. X'  where  G,^ x:V'' |- X' : V'
       If    G |- X : V1 & V2,
       then  X := <X',X''>  where G |- X' : V' and G |- X'' : V''

       Effects: X is instantiated
    *)
    (* possible optimization: lower all the way to base type in one step *)
    (* Currently we assume that no constraints are attached to variables of functional type *)
    (* This may or may not hold, so a match exception is raised otherwise *)
    and lower (EVar (r, V, nil)) = lower' (r, whnf (V, id))
    and lower' (r, (Pi ((D' as Dec _, _), V'), s')) = 
          (r := SOME (Lam (decSub (D', s'), newEVar (EClo (V', dot1 s')))))
      | lower' (r, (Pi ((D' as LDec _, _), V'), s')) = 
          (r := SOME (Lam (decSub (D', s'), newEVar (EClo (V', ldot1 s')))))
      | lower' (r, (With (V', V''), s')) = 
          (r := SOME (Pair (newEVar(EClo (V',s')), newEVar (EClo (V'',s')))))
      | lower' (r, (Top, s')) =
          (r := SOME (Unit))
        (* no other cases possible by well-typing invariant *)

    (* whnfRoot ((C, S), s) = (U', s')

       Invariant:
       If    G |- s : G1      G1 |- C : V
			      G1 |- S : V > W
       then  G |- s' : G'     G' |- U' : W'
       and   G |- W [s] = W' [s'] : L

       Effects: EVars may be instantiated when lowered
    *)
    and whnfRoot ((BVar (k), S), s)   =
        (case bvarSub (k, s)
	   of Idx (k) => (Root (BVar (k), SClo (S, s)), id)
	    | Exp (U,V) => whnfRedex (whnf (U, id), (S, s)))
      | whnfRoot ((FVar (name, V, s'), S), s) =
	 (Root (FVar (name, V, comp (s', s)), SClo (S, s)), id)
      | whnfRoot ((C, S), s) =
	 (Root (C, SClo (S, s)), id)

    (* whnf (U, s) = (U', s')

       Invariant:
       If    G |- s : G'    G' |- U : V
       then  G |- s': G''   G''|- U' : V'
       and   G |- V [s] == V' [s'] == V'' : L  
       and   G |- U [s] == U' [s'] : V'' 
       and   (U', s') whnf

       whnf = (L, s) | (Pi DP. U, s) | (LPi DP. U, s) | U' & U'' | T 
            | (Root(n,S), id) | (Root(c,S), id) | (Root(d,S), id) | (Root(F[s'], S), id)
            | (Lam D. U, s) | (LLam D. U, s) | <U',U''> | Unit
            | (X, s) where X is uninstantiated
    *)
    (*
       Possible optimization :
         Define whnf of Root as (Root (n , S [s]), id)
	 Fails currently because appendSpine does not necessairly return
         a closure  -- cs
	 Advantage: in unify, abstract... the spine needn't be treated
         under id, but under s
    *)
    and whnf (Us as (Uni _, s)) = Us
      | whnf (Us as (Pi _, s)) = Us
      | whnf (Us as (With _, s)) = Us
      | whnf (Us as (Top, s)) = Us
      | whnf (Root R, s) = whnfRoot (R, s)
      | whnf (Redex (U, S), s) = whnfRedex (whnf (U, s), (S, s))
      | whnf (Us as (Lam _, s)) = Us
      | whnf (Us as (Pair _, s)) = Us
      | whnf (Us as (Unit, s)) = Us
      | whnf (EVar (ref (SOME U), _, _), s) = whnf (U, s)
      (* | whnf (Us as (EVar _, s)) = Us *)
      (* --------------------------------------------------------- *)
      (* next two avoid calls to whnf (V, id), where V is type of X *)
      | whnf (Us as (EVar (r, Root _, _), s)) = Us 
      | whnf (Us as (EVar (r, Uni _, _), s)) = Us 
      | whnf (Us as (X as EVar (r, V, _), s)) = 
          (case whnf (V, id)
	     of (Pi _, _) => (lower X; whnf Us)
	      | (With _, _) => (lower X; whnf Us)
	      | _ => Us)
      (* --------------------------------------------------------- *)

      | whnf (EClo (U, s'), s) = whnf (U, comp (s', s)) 

    (* expandDefn (Root (Defn (d), S), s) = (U' ,s')
     
       Invariant:
       If    G |- s : G1     G1 |- S : V > W            ((d @ S), s) in whnf
                             .  |- d = U : V'  
       then  G |- s' : G'    G' |- U' : W'
       and   G |- V' == V [s] : L               (. instead of G? -ic?)
       and   G |- W' [s'] == W [s] == W'' : L
       and   G |- (U @ S) [s] == U' [s'] : W'
       and   (U', s') in whnf
    *)
    fun expandDefn (Root (Defn (d), S), s) = 
	  whnfRedex (whnf (constDefn (d), id), (S, s))

    (* inferSpine ((S, s1), (V, s2)) = (V', s')

       Invariant:
       If  G |- s1 : G1  and  G1 |- S : V1 > V1'
       and G |- s2 : G2  and  G2 |- V : L,  (V, s2) in whnf
       and G |- S[s1] : V[s2] > W  (so V1[s1] == V[s2] and V1'[s1] == W)
       then G |- V'[s'] = W
    *)
    fun inferSpine ((Nil, _), Vs) = Vs
      | inferSpine ((SClo (S, s'), s), Vs) = 
          inferSpine ((S, comp (s', s)), Vs)
      | inferSpine ((App (U, S), s1), (Pi ((Dec (_, V1), _), V2), s2)) =
	  inferSpine ((S, s1), whnf (V2, Dot (Exp (EClo (U, s1), V1), s2)))
      | inferSpine ((LApp (U, S), s1), (Pi ((LDec (_, V1), _), V2), s2)) =
	  inferSpine ((S, s1), whnf (V2, LDot (Exp (EClo (U, s1), V1), s2)))
      | inferSpine ((Pi1 S, s1), (With (V1,_), s2)) =
	  inferSpine ((S, s1), (V1, s2))
      | inferSpine ((Pi2 S, s1), (With (_,V2), s2)) =
	  inferSpine ((S, s1), (V2, s2))

    (* inferCon (C) = V  if C = c or C = d and |- C : V *)
    fun inferCon (Const (cid)) = constType (cid)
      | inferCon (Defn (cid)) = constType (cid)

    (* etaExpand' (U, (V,s)) = U'
           
       Invariant : 
       If    G |- U : V [s]   (V,s) in whnf
       then  G |- U' : V [s]
       and   G |- U == U' : V[s]
       and   (U', id) in whnf and U' in head-eta-long form
    *)
    (* quite inefficient, at the moment -cs *)
    fun etaExpand' (U, (Root _, s)) = U
      | etaExpand' (U, (Pi ((D as Dec _, _), V), s)) =
          Lam (decSub (D, s), 
	       etaExpand' (Redex (EClo (U, shift),
				  App (Root (BVar (1), Nil), Nil)), 
			   whnf (V, dot1 s)))
      | etaExpand' (U, (Pi ((D as LDec _, _), V), s)) =
          Lam (decSub (D, s), 
	       etaExpand' (Redex (EClo (U, shift), 
				  LApp (Root (BVar (1), Nil), Nil)),
			   whnf (V, ldot1 s)))
      | etaExpand' (U, (With (V', V''), s)) =
	  Pair (etaExpand' (Redex (U, Pi1 (Nil)), (V', s)),
		etaExpand' (Redex (U, Pi2 (Nil)), (V'', s)))
      | etaExpand' (U, (Top, s)) =
          Unit

    (* etaExpandRoot (Root(C, S)) = U' where C = c or C = d

       Invariant:
       If   G |- C @ S : V  where C = c or C = d
       then G |- U' : V
       and  G |- C @ S == U'
       and (U',id) in whnf and U' in head-eta-long form
    *)
    fun etaExpandRoot (U as Root(C, S)) =
          etaExpand' (U, inferSpine ((S, id), (inferCon(C), id)))
  in
      val whnf = whnf
      val expandDefn = expandDefn
      val etaExpandRoot = etaExpandRoot
  end
end;  (* functor Whnf *)
