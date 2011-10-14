(* Type Checking *)
(* Author: Carsten Schuermann *)

functor TypeCheck (structure IntSyn' : INTSYN
		   structure Conv : CONV
		     sharing Conv.IntSyn = IntSyn'
		   structure Whnf : WHNF
		     sharing Whnf.IntSyn = IntSyn' 
		   structure Print : PRINT
		     sharing Print.IntSyn = IntSyn')
  : TYPECHECK
  (* :> TYPECHECK where IntSyn = IntSyn' *) =
struct
  structure IntSyn = IntSyn'
  exception Error of string

  local 
    open IntSyn

    (* some well-formedness conditions are assumed for input expressions *)
    (* e.g. don't contain "Kind", Evar's are consistently instantiated, ... *)

    (* Linearity is *not* checked here *)

    (* checkExp (G, (U, s1), (V2, s2)) = ()

       Invariant: 
       If   G |- s1 : G1   
       and  G |- s2 : G2    G2 |- V2 : L
       returns () if there is a V1 s.t.
	    G1 |- U : V1
       and  G  |- V1 [s1] = V2 [s2] : L
       otherwise exception Error is raised
    *)
    fun checkExp (G, Us, Vs) =
      let 
	val Us' = inferExp (G, Us)
      in
	if Conv.conv (Us', Vs) then ()
	(* fix!!! -fp *)
 	else raise Error ("Type mismatch")
	  (* ^ ": " ^ (Tools.stringCtx (G)) ^ " |- " ^ 
	   (Tools.stringExp (EClo Us')) ^ " =/= " ^ (Tools.stringExp (EClo Vs))
	   *)
      end

    and inferUni (Type) = Kind
        (* impossible: Kind *)

    (* inferExp (G, (U, s)) = (V', s')

       Invariant: 
       If   G  |- s : G1
       then if G1 |- U : V   (U doesn't contain EVAR's, FVAR's) 
	    then  G  |- s' : G'     G' |- V' : L
	    and   G  |- V [s] = V'[s'] : L
	    else exception Error is raised.

       Note: s' = id whenever V' is Type or Kind    -ic?
     *)
    and inferExpW (G, (Uni (L), _)) = (Uni (inferUni L), id)
      | inferExpW (G, (Pi ((D as Dec _, _) , V), s)) = 
	  (checkDec (G, (D, s));
	   inferExp (Decl (G, decSub (D, s)), (V, dot1 s)))
      | inferExpW (G, (Pi ((D as LDec _, _) , V), s)) = 
	  (checkDec (G, (D, s));
	   inferExp (Decl (G, decSub (D, s)), (V, ldot1 s)))
      | inferExpW (G, (With (V', V''), s)) = 
	  (checkExp (G, (V', s), (Uni(Type), id)) ;
	   checkExp (G, (V'',s), (Uni(Type), id)) ;
	   (Uni(Type), id))   	                      (* correct? -ic? *)
      | inferExpW (_, (Top, _)) = (Uni (Type), id)
      | inferExpW (G, (Root (C, S), s)) = 
	  inferSpine (G, (S, s), Whnf.whnf (inferCon (G, C), id))
      | inferExpW (G, (Lam (D as Dec _, U), s)) =
	  (checkDec (G, (D, s)); 
	   (Pi ((decSub (D, s), Maybe),
		EClo (inferExp (Decl (G, decSub (D, s)), (U, dot1 s)))), id))
      | inferExpW (G, (Lam (D as LDec _, U), s)) =
	  (checkDec (G, (D, s)); 
	   (Pi ((decSub (D, s), No),
		 EClo (inferExp (Decl (G, decSub (D, s)), (U, ldot1 s)))),
	    id))
      | inferExpW (G, (Pair (U', U''), s)) =
	  let
	    val Vs' = inferExp (G, (U', s))
	    val Vs'' = inferExp (G, (U'', s))
	  in
	    (With (EClo Vs', EClo Vs''), id)
	  end
      | inferExpW (_, (Unit, _)) = (Top, id)
      (* no cases for Redex, EVars and EClo's *)

    (* inferExp (G, Us) = (V', s')

       Invariant: same as inferExp, argument is not in whnf 
    *)
    and inferExp (G, Us) = inferExpW (G, Whnf.whnf Us)

    (* inferSpine (G, (S, s1), (V, s2)) = (V', s')

       Invariant: 
       If   G |- s1 : G1  
       and  G |- s2 : G2  and  G2 |- V : L ,   (V, s) in whnf  
       and  (S,V  don't contain EVAR's, FVAR's) 
       then if   there ex V1, V1'  G1 |- S : V1 > V1'
	    then G |- s' : G'    and  G' |- V' : L
	    and  G |- V1 [s1]   = V [s2] : L
            and  G |- V1'[s1]   = V' [s'] : L
    *)
    and inferSpine (G, (Nil, _), Vs) = Vs
      | inferSpine (G, (SClo (S, s'), s), Vs) = 
	  inferSpine (G, (S, comp (s', s)), Vs)
      | inferSpine (G, (App (U, S), s1), (Pi ((Dec (_, V1), _), V2), s2)) =
	  (checkExp(G, (U, s1), (V1, s2));
	   inferSpine (G, (S, s1),
		       Whnf.whnf (V2, Dot (Exp (EClo (U, s1), V1), s2))))
	  (* G |- Pi (x:V1, V2) [s2] = Pi (x: V1 [s2], V2 [1.s2 o ^1] : L
	     G |- U [s1] : V1 [s2]
	     Hence
	     G |- S [s1] : V2 [1. s2 o ^1] [U [s1], id] > V' [s']
	     which is equal to
	     G |- S [s1] : V2 [U[s1], s2] > V' [s']

	     Note that G |- U[s1] : V1 [s2]
	     and hence V2 must be under the substitution    U[s1]: V1, s2
	  *)
      | inferSpine (G, (App (U , S), _), (V, s)) = (* V <> (Pi x:V1. V2, s) *)
	  raise  Error ("expression is applied, but not a function")
      | inferSpine (G, (LApp (U, S), s1), (Pi ((LDec (_, V1), _), V2), s2)) =
	  (checkExp(G, (U, s1), (V1, s2));
	   inferSpine (G, (S, s1),
		       Whnf.whnf (V2, LDot (Exp (EClo (U, s1), V1), s2))))
	  (* Same reasoning as above *)
      | inferSpine (G, (LApp (U , S), _), (V, s)) = (* V <> (LPi x:V1.V2, s) *)
	  raise  Error ("expression is applied, but not a linear function")
      | inferSpine (G, (Pi1 S, s1), (With (V', _), s2)) =
	  inferSpine (G, (S, s1), (V', s2))
      | inferSpine (G, (Pi1 S, _), (V, s)) =        (* V <> V' & V'', s) *)
	  raise  Error ("expression is projected, but not on a pair")
      | inferSpine (G, (Pi2 S, s1), (With (_, V''), s2)) =
	  inferSpine (G, (S, s1), (V'', s2))
      | inferSpine (G, (Pi2 S, _), (V, s)) =        (* V <> V' & V'', s) *)
	  raise  Error ("expression is projected, but not on a pair")

    (* inferCon (G, C) = V'

       Invariant: 
       If    G |- C : V  
       and  (C  doesn't contain FVars)
       then  G' |- V' : L      (for some level L) 
       and   G |- V = V' : L
       else exception Error is raised. 
    *)
    and inferCon (G, BVar (k')) =
         (case ctxDec (G, k')
	    of  Dec (_,V) => V
	     | LDec (_,V) => V)
      | inferCon (G, Const(c)) = constType (c)
      | inferCon (G, Defn(d))  = constType (d)
      (* no case for FVar *)

    (* checkDec (G, (x:V, s)) = B

       Invariant: 
       If G |- s : G1 
       then B iff G |- V[s] : type
    *)
    and checkDec (G, (Dec (_, V) ,s)) = checkExp (G, (V, s), (Uni (Type), id))
      | checkDec (G, (LDec (_, V) ,s)) = checkExp (G, (V, s), (Uni (Type), id))

    fun check (U, V) = checkExp (Null, (U, id), (V, id))
    fun infer U = EClo (inferExp (Null, (U, id)))

    fun checkCtx Null =  ()
      | checkCtx (Decl (G, D)) = (checkCtx G; checkDec (G, (D, id)))
    
  in
      val check = check
      val infer = infer
      val typeCheck = fn (G, (U, V)) => 
	                   (checkCtx G; checkExp (G, (U, id), (V, id)))
  end  (* local ... *)
end; (* functor TypeCheck *)
