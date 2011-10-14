(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)

functor Strictness (structure IntSyn' : INTSYN)
  : STRICTNESS
  (* :> STRICTNESS where IntSyn = IntSyn' *) = 
struct
  structure IntSyn = IntSyn'
  exception Error of string
    
  local
    open IntSyn
 
    (* Definition of normal form (nf) --- see abstract.fun *)

    (* checkDistinct (k, S) = B

       Invariant: 
       If  G, D |- S : V > V', S in nf
       then B iff S = (k1 ; k2 ;...; kn ; NIL), k distinct from every ki
     *)
    fun checkDistinct (_, Nil) = true
      | checkDistinct (k, App (Root (BVar (k'), Nil), S)) =
          (* possibly eta-contract? -fp *)
          k <> k' andalso checkDistinct (k, S)
      | checkDistinct (k, LApp (Root (BVar (k'), Nil), S)) =
          (* possibly eta-contract? -fp *)
          k <> k' andalso checkDistinct (k, S)
      | checkDistinct (k, Pi1 S) = checkDistinct (k, S)
      | checkDistinct (k, Pi2 S) = checkDistinct (k, S)
      | checkDistinct _ = false


    (* checkSpine (k, S) = B
       
       Invariant: 
       If  G, D |- S : V > V', S in nf
       and |D| = k
       then B iff S = (k1 ; k2 ;...; kn ; NIL), kn <= k, all ki pairwise
	    distinct
    *)
    fun checkSpine (_, Nil) = true
      | checkSpine (k, App (Root (BVar (k') ,Nil), S)) =
	  k' <= k andalso checkDistinct (k', S) andalso checkSpine (k, S)
      | checkSpine (k, LApp (Root (BVar (k') ,Nil), S)) =
	  k' <= k andalso checkDistinct (k', S) andalso checkSpine (k, S)
      | checkSpine (k, Pi1 S) = checkSpine (k, S)
      | checkSpine (k, Pi2 S) = checkSpine (k, S)
      | checkSpine _ = false

    (* relExpW (k, p, U) = B 
       
       Invariant:
       If  G, D |- U : V
       and U is in nf (normal form)
       and |D| = k
       then B iff U is strict in p
    *)
    fun relExp (_, _, Uni(_)) = false
      | relExp (k, p, Lam (D, U)) =
          (* checking D in this case might be redundant *)
          relDec (k, p, D) orelse relExp (k+1, p+1, U)
      | relExp (k, p, Pair (U', U'')) =
          relExp (k, p, U') orelse relExp (k, p, U'') (* ? -ic? *)
      | relExp (_, _, Unit) = false                   (* ? -ic? *)
      | relExp (k, p, Pi ((D, _), U)) =
	  relDec (k, p, D) orelse relExp (k+1, p+1, U)
      | relExp (k, p, With (U', U'')) =
          relExp (k, p, U') orelse relExp (k, p, U'') (* ? -ic? *)
      | relExp (_, _, Top) = false                    (* ? -ic? *)
      | relExp (k, p, Root (C, S)) =
	  (case C
	     of (BVar (k')) => 
	        if (k' = p) then checkSpine (k, S)
		else if (k' <= k) then relSpine (k, p, S)
		     else false
              | (Const (c)) => relSpine (k, p, S)
	      | (Defn (d))  => relSpine (k, p, S))
	      (* no other cases possible *)
    (* no other cases possible *)

    (* relSpine (k, S) = B 
       
       Invariant:
       If  G, D |- S : V > W
       and S is in nf (normal form)
       and |D| = k
       then B iff S is strict in k
    *)
    and relSpine (_, _, Nil) = false
      | relSpine (k, p, App (U, S)) = 
          relExp (k, p, U) orelse relSpine (k, p, S)
      | relSpine (k, p, LApp (U, S)) = 
          relExp (k, p, U) orelse relSpine (k, p, S)
      | relSpine (k, p, Pi1 S) = relSpine (k, p, S)
      | relSpine (k, p, Pi2 S) = relSpine (k, p, S)

    and relDec (k, p, Dec (_, V)) = relExp (k, p, V)
      | relDec (k, p, LDec (_, V)) = relExp (k, p, V)

    (* traverseFlex (p, U) = B

       Traverses the flexible abstractions in U.
       
       Invariant:
       If   G |-(p) U : V
       and  U is in nf
       then B iff p occurs in strict position in U which starts
	          with flexible abstractions
    *)	 
    fun traverseFlex (p, U as Root _) = relExp (0, p, U)
      | traverseFlex (p, Lam (D, U)) = traverseFlex (p+1, U)
      | traverseFlex (p, Pair (U', U'')) =
         traverseFlex (p, U') orelse traverseFlex (p, U'')
      | traverseFlex (_, Unit) = false

    (* relTop (U, V) = ()
       
       Invariant:
       If . |- U : V 
       and U is in nf (normal form)
       then function returns () if U satisfies the strictness property

       raises Error if U does not satisfy the strictness property
    *)
    fun relTop (Root (BVar _, _), Pi _) =
          raise Error "Strictness condition violated after eta-expansion"
      | relTop (Root _, _) = ()
      | relTop (Lam (D, U), Pi (_, V)) = 
	  if traverseFlex (1, U) then relTop (U, V)
	  else raise Error "Strictness condition violated"
      | relTop (Pair (U', U''), With (V', V'')) = 
	  (relTop (U', V') ; relTop (U'', V''))
      | relTop (Unit, Top) = ()
  in
    val check = relTop
  end
end;  (* functor Strictness *)
