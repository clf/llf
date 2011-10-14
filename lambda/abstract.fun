(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor Abstract (structure IntSyn' : INTSYN
		  structure Whnf    : WHNF
		    sharing Whnf.IntSyn = IntSyn'
		  structure Pattern : PATTERN
		    sharing Pattern.IntSyn = IntSyn'
		  structure Unify   : UNIFY
		    sharing Unify.IntSyn = IntSyn'
		  structure Constraints : CONSTRAINTS
		    sharing Constraints.IntSyn = IntSyn')
  : ABSTRACT
  (* :> ABSTRACT where IntSyn = IntSyn' *) =
struct

  structure IntSyn = IntSyn'
    
  exception Error of string
    
  local

    open IntSyn
    structure C = Constraints
      
    (* Intermediate Data Structure *)

    datatype EFVar =
      EV of Exp option ref * Exp	(* Y ::= (X , {G} V)  if G |- X : V *)
    | FV of name * Exp			(*     | (F , {G} V)  if G |- F : V *)

    (*
       We write {{H}} for the context of H, where EVars and FVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_H, {{S}}_H for the corresponding translation of an
       expression or spine.

       Just like contexts G, any H is implicitly assumed to be
       well-formed and in dependency order.

       We write  H ||- U  if all EVars and FVars in U are collected in H.
       In particular, . ||- U means U contains no EVars or FVars.  Similarly,
       for spines H ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
	   of nil => ()
	    | _ => raise Error "Unresolved constraints")

    (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
    fun eqEVar (EVar (r1, _, _)) (EV (r2,  _)) = (r1 = r2)
      | eqEVar _ _ = false

    (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
    fun eqFVar (FVar (n1, _, _)) (FV (n2,  _)) = (n1 = n2)
      | eqFVar _ _ = false

    (* exists P H = B
       where B iff H = H1, Y, H2  s.t. P Y  holds
    *)
    fun exists P H =
        let fun exists' (Null) = false
	      | exists' (Decl(H',Y)) = P(Y) orelse exists' (H')
	in
	  exists' H
	end

    (* Definition of normal form (nf)

	UA ::= L | Pi (DA,P). UA | LPi (DA,P). UA | UA' & UA'' | T
             | Root(n,SA) | Root(c,SA) | Root(d,SA) |
             | Lam DA. UA | LLam DA. UA | Pair (UA', UA'') | Unit
	DA ::= x:UA
	SA ::= Nil | App (UA, SA) | LApp (UA, SA) | Pi1 SA | Pi2 SA
    *)


    (* occursIn (k, U) = B, 

       Invariant:
       If    U in nf 
       then  B iff k occurs in U
    *)
    fun occursInExp (k, Uni _) = false
      | occursInExp (k, Pi (DP, V)) =
          occursInDecP (k, DP) orelse occursInExp (k+1, V)
      | occursInExp (k, With (V', V'')) =
          occursInExp (k, V') orelse occursInExp (k, V'')
      | occursInExp (_, Top) = false
      | occursInExp (k, Root (C, S)) =
	  occursInCon (k, C) orelse occursInSpine (k, S)
      | occursInExp (k, Lam (D,V)) =
	  occursInDec (k, D) orelse occursInExp (k+1, V)
      | occursInExp (k, Pair (V', V'')) =
	  occursInExp (k, V') orelse occursInExp (k, V'')
      | occursInExp (_, Unit) = false
      (* no case for Redex, EVar, EClo *)

    and occursInCon (k, BVar (k')) = (k = k')
      | occursInCon (k, Const _) = false
      | occursInCon (k, Defn _) = false
      (* no case for FVar *)

    and occursInSpine (_, Nil) = false
      | occursInSpine (k, App (U, S)) =
          occursInExp (k, U) orelse occursInSpine (k, S)
      | occursInSpine (k, LApp (U, S)) =
          occursInExp (k, U) orelse occursInSpine (k, S)
      | occursInSpine (k, Pi1 (S)) = occursInSpine (k, S)
      | occursInSpine (k, Pi2 (S)) = occursInSpine (k, S)
      (* no case for SClo *)

    and occursInDec (k, Dec (_, V)) = occursInExp (k, V)
      | occursInDec (k, LDec(_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise 
    *)
    fun piDepend (DPV as ((D, No), V)) = Pi DPV
      | piDepend (DPV as ((D, Maybe), V)) = 
        if occursInExp (1, V)
	  then Pi DPV			(* cosmetic change -ic *)
	else Pi ((D, No), V)

    (* raiseType (G, (V, s)) = V'
     
       Invariant: 
       If   G |- s : G'     G' |- V : L
       then V' = {G'} V
       and  . |- V' : L
    *)
    fun raiseType (G, (V, s)) = 
      let 
	val depth = ctxLength (G)
	fun raiseType' (Shift (k), V) =
	    if k < depth
	      then raiseType' (Dot (Idx (k+1), Shift (k+1)), V)
	    else (* k = depth *) V
	  | raiseType' (Dot (Idx (k), s'), V) =
            let val D =
	          if Pattern.checkSub s' (* checked over and over? -ic *)
		    then let
			   val Dec (name, V) =  ctxDec (G, k)
			       (* must be intuitionistic *)
			 in (* must succeed ---
			       do not handle Unify.NonInvertible *)
			   Dec (name, Unify.safeInvertExp((V, id), s'))
			 end
		  else raise Error "Mixed substitution cannot be raised"
	    in
	      raiseType' (s', Pi ((D, Maybe), V))
	    end
	  | raiseType' (Dot (Exp (_, V'), s'), V) =
	      raiseType' (s', Pi  ((Dec (NONE, V'), Maybe), V))
	  | raiseType' (LDot (Idx (k), s'), V) =
            let val D =
	          if Pattern.checkSub s' (* checked over and over? -ic *)
		    then
		      (case ctxDec (G, k)   (* correct? -ic *)
			 of LDec (name, V) =>
			     LDec (name, Unify.safeInvertExp((V, id), s'))
			     (* must succeed --- do not handle Unify.NonInvertible *)
			  | Dec (name, V) =>
			     Dec (name, Unify.safeInvertExp((V, id), s')))
			     (* must succeed --- do not handle Unify.NonInvertible *)
		  else raise Error "Mixed substitution cannot be raised"
	    in
	      raiseType' (s', Pi ((D, No), V))
	    end
	  | raiseType' (LDot (Exp (_, V'), s'), V) =
	      raiseType' (s', Pi  ((LDec (NONE, V'), No), V))
      in
	raiseType' (s, V)
      end

    (* collectExpW (G, (U, s), H) = H'

       Invariant: 
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   H' = H, H''
	     where H'' contains all EVars and FVars in (U,s)
    *)
    (* Possible optimization: Calculuate also the normal form of the term *)
    fun collectExpW (G, (Uni L, s), H) = H
      | collectExpW (G, (Pi ((D as Dec _, _), V), s), H) =
          collectExp (Decl (G, decSub (D, s)),
		      (V, dot1 s),
		      collectDec (G, (D, s), H))
      | collectExpW (G, (Pi ((D as LDec _, _), V), s), H) =
          collectExp (Decl (G, decSub (D, s)),
		      (V, ldot1 s),
		      collectDec (G, (D, s), H))
      | collectExpW (G, (With (V', V''), s), H) =
          collectExp (G, (V'', s), collectExp (G, (V', s), H))
      | collectExpW (_, (Top, _), H) = H
      | collectExpW (G, (Root (F as FVar (name, V, s'), S), s), H) =
	if exists (eqFVar F) H
	  then collectSpine (G, (S, s), H)
	else (* s' = ^|G| *)
	  collectSpine (G, (S, s),
			Decl (collectExp (Null, (V, id), H), FV (name, V)))
      | collectExpW (G, (Root (_ , S), s), H) =
	  collectSpine (G, (S, s), H)
      | collectExpW (G, (Lam (D as Dec _, U), s), H) =
	  collectExp (Decl (G, decSub (D, s)),
		      (U, dot1 s),
		      collectDec (G, (D, s), H))
      | collectExpW (G, (Lam (D as LDec _, U), s), H) =
	  collectExp (Decl (G, decSub (D, s)),
		      (U, ldot1 s),
		      collectDec (G, (D, s), H))
      | collectExpW (G, (Pair (U', U''), s), H) =
          collectExp (G, (U'', s), collectExp (G, (U', s), H))
      | collectExpW (_, (Unit, _), H) = H
      | collectExpW (G, (X as EVar (r, V, Cnstr), s), H) =
	  if exists (eqEVar X) H
	    then collectSub(G, s, H)
	  else let
	         val _ = checkEmpty Cnstr
		 val V' = raiseType(G, (V, s))
	       in
		 collectSub(G, s,
			    Decl (collectExp (Null, (V', id), H), EV(r, V')))
	       end
      (* No other cases can occur due to whnf invariant *)

    (* collectExp (G, (U, s), H) = H' 
       
       same as collectExpW  but  (U,s) need not to be in whnf 
    *) 
    and collectExp (G, Us as (U, s), H) = collectExpW (G, Whnf.whnf Us, H)

    (* collectSpine (G, (S, s), H) = H' 

       Invariant: 
       If    G |- s : G1     G1 |- S : V > P
       then  H' = H, H''
       where H'' contains all EVars and FVars in (S, s)
     *)
    and collectSpine (G, (Nil, _), H) = H
      | collectSpine (G, (SClo(S, s'), s), H) = 
          collectSpine (G, (S, comp (s', s)), H)
      | collectSpine (G, (App (U, S), s), H) =
	  collectSpine (G, (S, s), collectExp (G, (U, s), H))
      | collectSpine (G, (LApp (U, S), s), H) =
	  collectSpine (G, (S, s), collectExp (G, (U, s), H))
      | collectSpine (G, (Pi1 S, s), H) =
	  collectSpine (G, (S, s), H)
      | collectSpine (G, (Pi2 S, s), H) =
	  collectSpine (G, (S, s), H)

    (* collectDec (G, (x:V, s), H) = H'

       Invariant: 
       If    G |- s : G1     G1 |- V : L
       then  H' = H, H''
       where H'' contains all EVars and FVars in (V, s)
    *)
    and collectDec (G, (Dec (_, V), s), H) = collectExp (G, (V, s), H)
      | collectDec (G, (LDec (_, V), s), H) = collectExp (G, (V, s), H)

    (* collectSub (G, s, H) = H' 

       Invariant: 
       If    G |- s : G1    
       then  H' = H, H''
       where H'' contains all EVars and FVars in s
    *)
    and collectSub (G, Shift _, H) = H
      | collectSub (G, Dot (Idx _, s), H) = collectSub (G, s, H)
      | collectSub (G, Dot (Exp (U, V), s), H) =
	  (* collect V in next line? *)
          (* typing invariant guarantees that V makes sense already? *)
	  collectSub (G, s, collectExp (G, (U, id), H))
	  (* collectExp (G, (V, s), H) *)
      | collectSub (G, LDot (Idx _, s), H) = collectSub (G, s, H)
      | collectSub (G, LDot (Exp (U, V), s), H) =
	  (* collect V in next line? *)
          (* typing invariant guarantees that V makes sense already? *)
	  collectSub (G, s, collectExp (G, (U, id), H))
	  (* collectExp (G, (V, s), H) *)

    (* abstractEVar (H, depth, X) = C'
     
       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in H  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{H}}, G |- C' : V
    *)
    fun abstractEVar (Decl (H', EV (r', _)), depth, X as EVar (r, _, _)) =
          if r = r' then BVar (depth+1)
	  else abstractEVar (H', depth+1, X)
      | abstractEVar (Decl (H', FV (n', _)), depth, X) = 
	  abstractEVar (H', depth+1, X)

    (* abstractFVar (H, depth, F) = C'
     
       Invariant:
       If   G |- F : V
       and  |G| = depth
       and  F occurs in H  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{H}}, G |- C' : V
    *)
    fun abstractFVar (Decl(H', EV _), depth, F) =
  	  abstractFVar (H', depth+1, F)
      | abstractFVar (Decl(H', FV (n', _)), depth, F as FVar (n, _, _)) = 
	  if n = n' then BVar (depth+1)
	  else abstractFVar (H', depth+1, F)
 
    (* abstractExpW (H, depth, (U, s)) = U'
       U' = {{U[s]}}_H

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   H is internal context in dependency order
       and   |G| = depth
       and   H ||- U and H ||- V
       then  {{H}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf 
    *)
    fun abstractExpW (H, depth, (U as Uni (L), s)) = U
      | abstractExpW (H, depth, (Pi ((D as Dec _, P), V), s)) =
          piDepend ((abstractDec (H, depth, (D, s)), P), 
		    abstractExp (H, depth + 1, (V, dot1(s))))
      | abstractExpW (H, depth, (Pi ((D as LDec _, P), V), s)) =  (* P = no *)
	  Pi ((abstractDec (H, depth, (D, s)), P), 
		    abstractExp (H, depth + 1, (V, ldot1(s))))
      | abstractExpW (H, depth, (With (V', V''), s)) =
	  With (abstractExp (H, depth, (V', s)),
		abstractExp (H, depth, (V'', s)))
      | abstractExpW (_, _, (Top, _)) = Top
      | abstractExpW (H, depth, (Root (F as FVar _, S), s)) =
	  Root (abstractFVar (H, depth, F), 
		abstractSpine (H, depth, (S, s)))
      | abstractExpW (H, depth, (Root (C, S) ,s)) =
	  Root (C, abstractSpine (H, depth, (S, s)))   
      | abstractExpW (H, depth, (Lam (D as Dec _, U), s)) =
          Lam (abstractDec (H, depth, (D, s)),
	       abstractExp (H, depth + 1, (U, dot1(s))))
      | abstractExpW (H, depth, (Lam (D as LDec _, U), s)) =
          Lam (abstractDec (H, depth, (D, s)),
	        abstractExp (H, depth + 1, (U, ldot1(s))))
      | abstractExpW (H, depth, (Pair (U', U''), s)) =
	  Pair (abstractExp (H, depth, (U', s)),
		abstractExp (H, depth, (U'', s)))
      | abstractExpW (_, _, (Unit, _)) = Unit
      | abstractExpW (H, depth, (X as EVar _, s)) =
 	  Root (abstractEVar (H, depth, X), 
		abstractSub (H, depth, s, Nil))

    (* abstractExp (H, depth, (U, s)) = U'
     
       same as abstractExpW, but (U,s) need not to be in whnf 
    *)
    and abstractExp (H, depth, Us) = abstractExpW (H, depth, Whnf.whnf Us)

    (* abstractSub (H, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_H @@ S

       Invariant:
       If   G |- s : G1   
       and  |G| = depth
       and  H ||- s
       then {{H}}, G |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
    and abstractSub (H, depth, Shift (k), S) = 
	if k < depth
	  then abstractSub (H, depth, Dot (Idx (k+1), Shift (k+1)), S)
	else (* k = depth *) S
      | abstractSub (H, depth, Dot (Idx (k), s), S) =
	  abstractSub (H, depth, s, App (Root (BVar (k), Nil), S))
      | abstractSub (H, depth, Dot (Exp (U, _), s), S) =
	  abstractSub (H, depth, s, App (abstractExp (H, depth, (U, id)), S))
      | abstractSub (H, depth, LDot (Idx (k), s), S) =
	  abstractSub (H, depth, s, LApp (Root (BVar (k), Nil), S))
      | abstractSub (H, depth, LDot (Exp (U, _), s), S) =
	  abstractSub (H, depth, s, LApp (abstractExp (H, depth, (U, id)), S))
 
    (* abstractSpine (H, depth, (S, s)) = S'
       where S' = {{S[s]}}_H

       Invariant:
       If   G |- s : G1     G1 |- S : V > P 
       and  H ||- S
       and  |G| = depth

       then {{H}}, G |- S' : V' > P'
       and  . ||- S'
    *)
    and abstractSpine (H, depth, (Nil, _))  = Nil 
      | abstractSpine (H, depth, (SClo (S, s'), s)) = 
	  abstractSpine (H, depth, (S, comp (s', s)))
      | abstractSpine (H, depth, (App (U, S), s)) =
	  App (abstractExp (H, depth, (U ,s)), 
	       abstractSpine (H, depth, (S, s)))
      | abstractSpine (H, depth, (LApp (U, S), s)) =
	  LApp (abstractExp (H, depth, (U ,s)), 
	        abstractSpine (H, depth, (S, s)))
      | abstractSpine (H, depth, (Pi1 S, s)) =
	  Pi1 (abstractSpine (H, depth, (S, s)))
      | abstractSpine (H, depth, (Pi2 S, s)) =
	  Pi2 (abstractSpine (H, depth, (S, s)))

    (* abstractDec (H, depth, (x:V, s)) = x:V'
       where V = {{V[s]}}_H

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  H ||- V
       and  |G| = depth

       then {{H}}, G |- V' : L
       and  . ||- V'
    *)
    and abstractDec (H, depth, (Dec (x, V), s)) =
	  Dec (x, abstractExp (H, depth, (V, s)))
      | abstractDec (H, depth, (LDec (x, V), s)) =
	  LDec (x, abstractExp (H, depth, (V, s)))

    (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'

       Is this function more general than necessary? -ic?
    *)
    fun getLevel (Uni _) = Kind 
      | getLevel (Pi ((Dec _, _), U)) = getLevel U
      | getLevel (Pi ((LDec _, _), U)) =  Type
      | getLevel (With (U', U'')) =  Type
      | getLevel (Top) = Type
      | getLevel (Root _)  = Type
      | getLevel (Redex (U, _)) = getLevel U
      | getLevel (Lam (_, U)) = getLevel U    (* can it occurr? -ic *)
      | getLevel (Pair (U', _)) = getLevel U' (* can it occurr? -ic *)
      | getLevel (Unit) = Type                (* can it occurr? -ic *)
      | getLevel (EClo (U,_)) = getLevel U

    (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    *)
    fun checkType V = 
        (case getLevel V
	   of Type => ()
	    | _ => raise Error "Uninstantiated type variable")

    (* abstractHPi (H, V) = V'
       where V' = {{H}} V

       Invariant: 
       If   {{H}} |- V : L 
       and  . ||- V                (H instead of .?  -ic)

       then V' = {{H}} V
       and  . |- V' : L
       and  . ||- V'
    *)
    fun abstractHPi (Null, V) = V
      | abstractHPi (Decl(H', EV (_, V')), V) =
        let
	  val V'' = abstractExp (H', 0, (V', id))
	  val _ = checkType V''	
	in
	  abstractHPi (H', Pi ((Dec(NONE, V''), Maybe), V))
	end
      | abstractHPi (Decl(H', FV (name,V')), V) =
	let
	  val V'' = abstractExp (H', 0, (V', id))
	  val _ = checkType V''
	in
	  abstractHPi (H', Pi ((Dec(SOME(name), V''), Maybe), V))
	end
      (* No linear case  -ic *)

    (* abstractHLam (H, U) = U'
       where U' = [[H]] U

       Invariant: 
       If   {{H}} |- U : V 
       and  . ||- U                (H instead of .?  -ic)
       and  . ||- V                (H instead of .?  -ic)

       then U' = [[H]] U
       and  . |- U' : {{H}} V
       and  . ||- U'
    *)
    fun abstractHLam (Null, U) = U
      | abstractHLam (Decl(H', EV (_,V')), U) =
          abstractHLam (H', Lam (Dec(NONE, abstractExp (H', 0, (V', id))), U))
      | abstractHLam (Decl(H', FV (name,V')), U) =
 	  abstractHLam (H', Lam (Dec(SOME(name),
				     abstractExp (H', 0, (V', id))), U))

    (* abstractDecl V = (k', V')

       Invariant: 
       If    . |- V : L
       and   H ||- V

       then  . |- V' : L
       and   V' = {{H}} V
       and   . ||- V'
       and   k' = |H|
    *)
    fun abstractDecl V =
        let
	  val H = collectExp (Null, (V, id), Null)
	in
	  (ctxLength H, abstractHPi (H, abstractExp (H, 0, (V, id))))
	end 

    (* abstractDefn  (U, V) = (k', (U', V'))

       Invariant: 
       If    . |- V : L
       and   . |- U : V
       and   H1 ||- V
       and   H2 ||- U
       and   H = H1, H2

       then  . |- V' : L
       and   V' = {{H}} V
       and   . |- U' : V'
       and   U' = [[H]] U
       and   . ||- V'
       and   . ||- U'
       and   k' = |H|
    *)
    fun abstractDefn (U, V) =
        let
	  val H = collectExp (Null, (U, id), collectExp (Null, (V, id), Null))
	in
	  (ctxLength H, (abstractHLam (H, abstractExp (H, 0, (U, id))), 
			    abstractHPi  (H, abstractExp (H, 0, (V, id)))))
	end 
  in
    val raiseType = raiseType
    val piDepend = piDepend

    val abstractDecl = abstractDecl
    val abstractDefn = abstractDefn
  end
end;  (* functor Abstract *)
