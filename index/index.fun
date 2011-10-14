(* Indexing and Subordination *)
(* Author: Carsten Schuermann *)

functor Index (structure Global : GLOBAL
	       structure IntSyn': INTSYN
	       structure Whnf : WHNF
		 sharing Whnf.IntSyn = IntSyn'
	       val SO : bool)
  : INDEX
  (* :> INDEX where IntSyn = IntSyn' *) =
struct
  structure IntSyn = IntSyn'

  datatype Sgn =			(* Signature bins             *)
    Empty				(* S ::= .                    *)
  | Entry of IntSyn.cid * Sgn		(*     | cid, S               *)
 
  local
    structure I = IntSyn

    (* Signature bin array                             

       Invariant: 
       For all i: 
       If   binArray (i) = B =/= . 
       then for all c: V in B : i in target (V)
    *)

    val binArray = Array.array (Global.maxCid + 1, Empty)

    (* Subordination array

       Invariant:
       For all a:
       If   soArray (a) = A 
       then for all a':K in A
            a' <* a  (a transively subordinates a' 
	              or a' is subordinate to a)
    *)

    val soArray : (IntSyn.cid list) Array.array    
          = Array.array (Global.maxCid + 1, nil) 
      
    (* reset () = ()

       Invariant:
       Empties subordination array/signature bin array
    *)
      
    fun reset () = 
      (Array.modify (fn _ => Empty) binArray;
       Array.modify (fn _ => nil) soArray)
      
    (* targetFamDec (x:V) = As, the target families of V *)
    fun targetFamDec (I.Dec (_, V)) = I.targetFamList V
      | targetFamDec (I.LDec (_,V )) = I.targetFamList V

    (* prefixDistinct (Bs, As) = As'
       As' results from adding to the front of As every element of Bs
       that does not appear in As
    *)
    fun prefixDistinct (nil, A) = A
      | prefixDistinct (b :: Bs, A) =
         if List.exists (fn x => x = b) A
	   then prefixDistinct (Bs, A)
	 else b :: prefixDistinct (Bs, A)

    (* collectTypeW ((V, s), A) = A'
 
       Invariant:
       If   G |- s : G'  G' |- V : L   (V, s) in whnf
       and  A set of type constants (not a multiset)
       then A' = A, A''
       and  a in A'' iff a does not occur in A and a is
	    a target type of some argument type of V
    *)

    fun collectTypeW ((I.Uni L, s), A) = A
      | collectTypeW ((I.Top, s), A) = A
      | collectTypeW ((I.With(V1,V2), s), A) =
         collectType ((V2,s), collectType ((V1,s), A))
      | collectTypeW ((I.Pi ((I.Dec (_, V1), P), V2), s), A) =
	 collectType ((V2, I.dot1 s),
		      prefixDistinct (valOf (I.targetFamList V1), A))
      | collectTypeW ((I.Pi ((I.LDec (_, V1), P), V2), s), A) =
	 collectType ((V2, I.ldot1 s),
		      prefixDistinct (valOf (I.targetFamList V1), A))
      (* no other cases possible *)
 
    (* collectType, same as collectTypeW, but argument (V, s) not necessarily
       in whnf
     *)
    and collectType (Vs, A) = collectTypeW (Whnf.whnf Vs, A)


    (* distribute (As, Bs, Zs) = Cs
       Cs = Ds @ Zs
       Ds is a list containing the cartesian product of As and Bs
    *)       
    fun cartesian (As, Bs, Zs) =
         let
	   fun cartesian' (nil, Cs) = Cs
	     | cartesian' (a::As, Cs) =
	        let
		  fun cart' (nil, Cs) = Cs
		    | cart' (b::Bs, Cs) = (a,b) :: cart' (Bs, Cs)
		in
		  cartesian' (As, cart'(Bs, Cs))
		end
	 in
	   cartesian' (As, Zs)
	 end


    (* slightly modified version of typechecking *)
    (* collectExp (G, (U, s1), A) = A'

       Invariant: 
       If   G |- s1 : G1  and  G1 |- U1 : V1   
       and  A set of pairs of type constants (not a multiset)
       then A' = A, A'' 
       and  A'' = {(a, b) | forall a,b s.t. a < (U1[s1] : V1[s1]) b} 
       (note: subordination relation <, follows ideas developed in [Virga 96])
    *)

    fun collectExp (G, Us, A) =
      let 
	val (Us', A') = inferExp (G, Us, A)
      in
	A'   (* Us' == Vs  by invariant *) 
      end

    and inferUni (I.Type, A) = ((I.Uni (I.Kind), I.id), A)
        (* impossible: Kind *)

    (* inferExp (G, (U, s), A) = ((V', s'), A')

       Invariant: 
       If   G  |- s : G1, and G1 |- U : V  and  (U, s) in  whnf
       and  A set of pairs of type constants (not a multiset)
       then G  |- s' : G'     G' |- V' : L
       and  G  |- V [s] = V'[s'] : L
       and  A' = A, A'' 
       and  A'' = {(a, b) | forall a, b s.t. a < (U[s] : V[s]) b} 
	    
     *)
    and inferExpW (G, (I.Uni (L), _), A ) = (inferUni (L, A))
      | inferExpW (G, (I.Top, s), A) = ((I.Uni(I.Type), I.id), A)
      | inferExpW (G, (I.With (V1, V2), s), A) =
         let
	   val (_, A') = inferExp (G, (V1, s), A)  (* _ = (Uni(Type), id) *)
	 in
	   inferExp (G, (V2, s), A')          (* = ((Uni(Type), id), A'') *)
	 end
      | inferExpW (G, (I.Pi ((D as I.Dec _, _) , V), s), A) = 
          inferExp (I.Decl (G, I.decSub (D, s)),
		    (V, I.dot1 s),
		    collectDec (G, (D, s),              (* ? -ic *)
				cartesian (valOf (targetFamDec D),
					   valOf (I.targetFamList V), A)))
      | inferExpW (G, (I.Pi ((D as I.LDec _, _) , V), s), A) = 
          inferExp (I.Decl (G, I.decSub (D, s)),
		    (V, I.ldot1 s),
		    collectDec (G, (D, s),              (* ? -ic *)
				cartesian (valOf (targetFamDec D),
					   valOf (I.targetFamList V), A)))
      | inferExpW (G, (I.Root (C, S), s), A) =
	  inferSpine (G, (S, s), Whnf.whnf (inferCon (G, C), I.id), A)
      | inferExpW (G, (I.Unit, s), A) = ((I.Top, I.id), A)
      | inferExpW (G, (I.Pair (U1, U2), s), A) =
	  let
	    val (Vs1, A1) = inferExp (G, (U1, s), A)
	    val (Vs2, A2) = inferExp (G, (U2, s), A1)
	  in
	    ((I.With (I.EClo Vs1, I.EClo Vs2), I.id), A2)
	  end
      | inferExpW (G, (I.Lam (D as I.Dec _, U), s), A) = (* collect here *)
	  let 
	    val (Vs' as (V,s'), A') = inferExp (I.Decl (G, I.decSub (D, s)),
						(U, I.dot1 s), A)
	  in
	    ((I.Pi ((I.decSub (D, s), I.Maybe), I.EClo Vs'), I.id), 
	     collectDec (G, (D, s),                     (* ? -ic *)
			 cartesian (valOf (targetFamDec D),
				    valOf (I.targetFamList V), A')))
	  end
      | inferExpW (G, (I.Lam (D as I.LDec _, U), s), A) = (* collect here *)
	  let 
	    val (Vs' as (V,s'), A') = inferExp (I.Decl (G, I.decSub (D, s)),
						(U, I.ldot1 s), A)
	  in
	    ((I.Pi ((I.decSub (D, s), I.No), I.EClo Vs'), I.id), 
	     collectDec (G, (D, s),                     (* ? -ic *)
			 cartesian (valOf (targetFamDec D),
				    valOf (I.targetFamList V), A')))
	  end

    (* inferExp (G, Us, A) = (Vs', A')

       Invariant: same as inferExp, argument is not in whnf 
    *)
    and inferExp (G, Us, A) = inferExpW (G, Whnf.whnf Us, A)

    (* inferSpine (G, (S, s1), (V, s2)) = (V', s')

       Invariant: 
       If   G |- s1 : G1  and  G1 |- S : V1 > V1'
       and  G |- s2 : G2  and  G2 |- V : L ,   (V, s) in whnf  
       and  A set of pairs of type constants (not a multiset)
       and  (S,V  don't contain EVAR's, FVAR's) 
       then ex G |- s' : G'    and  G' |- V' : L
       and  G |- V1 [s1]   = V [s2] : L
       and  G |- V1'[s1]   = V' [s'] : L
       and  A' = A, A'' 
       and  A'' = {(a, b) | forall a, b s.t. a < (U[s] : V[s]) b} 
    *)
    and inferSpine (G, (I.Nil, _), Vs, A) = (Vs, A)
      | inferSpine (G, (I.SClo (S, s'), s), Vs, A) = 
	  inferSpine (G, (S, I.comp (s', s)), Vs, A) 
      | inferSpine (G, (I.App(U,S), s1), (I.Pi((I.Dec(_,V1), _), V2), s2), A) =
	  inferSpine (G, (S, s1),
		      Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s1), V1), s2)),
		      collectExp(G, (U, s1), A))
      | inferSpine (G, (I.LApp(U,S), s1), (I.Pi((I.LDec(_,V1),_),V2), s2), A) =
	  inferSpine (G, (S, s1),
		      Whnf.whnf (V2, I.LDot (I.Exp (I.EClo (U, s1), V1), s2)),
		      collectExp(G, (U, s1), A))
      | inferSpine (G, (I.Pi1 S, s1), (I.With (V1, _), s2), A) =
	  inferSpine (G, (S, s1), (V1, s2), A)
      | inferSpine (G, (I.Pi2 S, s1), (I.With (_, V2), s2), A) =
	  inferSpine (G, (S, s1), (V2, s2), A)

    (* inferCon (G, C) = V'

       Invariant: 
       If    G |- C : V  
       and  (C  doesn't contain FVars)
       then  G' |- V' : L      (for some level L) 
       and   G |- V = V' : L
    *)
    and inferCon (G, I.BVar (k')) = 
          let 
	    val P = I.ctxDec (G, k')
	  in
	    case P
	      of I.Dec  (_,V) => V
	       | I.LDec (_,V) => V
	  end
      | inferCon (G, I.Const(c)) = I.constType (c)
      | inferCon (G, I.Defn(d))  = I.constType (d)
      (* no case for FVar *)

    (* collectDec (G, (x:V, s), A) = A'

       Invariant: 
       If   G |- s : G1 and G |- V[s] : type 
       and  A set of pairs of type constants (not a multiset)
       and  A' = A, A'' 
       and  A'' = {(a, b) | forall a, b s.t. a < (V[s] : type) b} 
    *)
    and collectDec (G, (I.Dec (_, V) ,s), A) = collectExp (G, (V, s), A)
      | collectDec (G, (I.LDec (_, V) ,s), A) = collectExp (G, (V, s), A)

    (* collect c = ()

       Invariant: 
       If Sigma (c) = K
       then subordination Array (c) is updated with 
	   subordination information from K
       If Sigma (c) = A
       then subordination Array (c) is updated with 
	   subordination information from A
    *)

    fun collect cid =
      let 
	val V = I.constType cid 
	fun distribute nil = ()
	  | distribute ((a, b) :: A) =
	      (if List.exists (fn x => x = a) (Array.sub (soArray, b)) then ()
	       else Array.update (soArray, b, a :: (Array.sub (soArray, b)));
		 distribute A)
      in
	case I.targetFamList V
	  of NONE => Array.update (soArray, cid, collectType ((V, I.id), nil))
	   | SOME cs => distribute (collectExp (I.Null, (V, I.id), nil))
      end


    (* transClosure () = ()

       Invariant:
       The subordination Array is closed under transitivity
    *)

    fun transClosure () = 
      let 
	fun close'' (c, nil) = true
	  | close'' (c, a :: A') = 
              if (List.exists (fn x => x = a) (Array.sub (soArray, c))) 
		then close'' (c, A')
	      else (Array.update (soArray, c, a :: Array.sub (soArray, c));
		    close'' (c, A'); false)

	fun close' (c, nil) =
              true
	  | close' (c, a :: A) =
	      (close'' (c, Array.sub (soArray, a))) andalso (close' (c, A))
  
	fun close (c, A) = 
	  if close' (c, A) then ()
	  else close (c, A)  (* transitive closure will eventually terminate *)

	fun transClosure' c = 
	  if c < 0 then ()
	  else 
	    (transClosure' (c-1);
	     case Array.sub (soArray, c) of 
	       nil => ()
	     | A => close (c, A))
      in
	transClosure'  (I.sgnSize () - 1)
      end

    (* compile () = ()
     
       Invariant:
       Calculates the content of the signature bin array
    *)

    fun compile () =
      let 
	fun update (cid, NONE) = ()
	  | update (cid, SOME cids) = 
	     let
	       fun update' nil = ()
		 | update' (cid' :: cids) =
		     (Array.update (binArray, cid', 
				    Entry (cid, Array.sub (binArray, cid'))) ;
		      update' cids)
	     in
	       update' cids
	     end
	fun compile' cid = 
	  if cid < 0 then ()
	  else  
	    (update (cid, I.targetFamList (I.constType cid)); 
	     compile' (cid - 1);
	     collect cid)
      in
	compile' (I.sgnSize () - 1)
      end

    fun lookup cid = Array.sub (binArray, cid)

    infix <*
    infix ==
    infix <<


    (* a <* b = B'

       Invariant:
       If   Sigma (a) = K1 and  Sigma (b) = K2
       then B' = true :iff a is subordinated by b
    *)
    fun (a <* b) = List.exists (fn x => x = a)  (Array.sub (soArray, b))

    (* a <* b = B'

       Invariant:
       If   Sigma (a) = K1 and  Sigma (b) = K2
       then B' = true :iff a <* b and b <* a
    *)
    fun (a == b) = (a <* b) andalso (b <* a)

    (* a << b :iff B'

       Invariant: 
       If   Sigma (a) = K1 and  Sigma (b) = K2
       then B' = true :iff a is immediately subordinated by b *)
    fun (a << b) = List.exists (fn x => x = a)
                      (collectType ((I.constType b, I.id), nil))

    (* temporary  ????? to be removed *)		      
    fun get c = 
      map (fn x => (I.entryName (I.sgnLookup x)))
          (Array.sub (soArray, c))
  in
    val reset = reset
    val compile = fn () => (compile (); transClosure ())
    val lookup = lookup
    val op<* = fn (x, y) => if SO then x <* y else true
    val op== = fn (x, y) => x == y 
    val op<< = fn (x, y) => x << y
    val get = get
  end (* local *)
end; (* functor Index *)
