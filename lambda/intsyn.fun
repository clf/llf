(* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor IntSyn (structure Global : GLOBAL) :> INTSYN =
struct

  type cid = int			(* Constant identifier        *)
  type name = string			(* Variable name              *)

  (* Contexts *)

  datatype 'a Ctx =			(* Contexts                   *)
    Null				(* G ::= .                    *)
  | Decl  of 'a Ctx * 'a	       	(*     | G, D                 *)


  (* ctxPop (G) => G'
     Invariant: G = G',D
     Effect: raises Match, if invariant violated
  *)
  fun ctxPop (Decl (G, D)) = G

  (* ctxLookup (G, k) = D, k counting 
     Invariant: 1 <= k <= |G|, where |G| is length of G
  *)
  fun ctxLookup (G, k) =
      let (* ctxLookup' (G'', k') = D
	     where 1 <= k' <= |G''|
           *)
	fun ctxLookup' (Decl (G', D), 1) = D
	  | ctxLookup' (Decl (G', _), k') = ctxLookup' (G', k'-1)
	 (* ctxLookup' (Null, k')  should not occur by invariant *)
      in
	ctxLookup' (G, k)
      end

  (* ctxLength G = |G|, the number of declarations in G *)
  fun ctxLength G =
      let 
	fun ctxLength' (Null, n) = n
	  | ctxLength' (Decl(G, _), n) = ctxLength' (G, n+1)
      in
	ctxLength' (G, 0)
      end

  datatype Depend =                     (* Dependency information     *)
    No                                  (* P ::= No                   *)
  | Maybe                               (*     | Maybe                *)

  (* Expressions *)

  datatype Uni =			(* Universes:                 *)
    Kind				(* L ::= Kind                 *)
  | Type				(*     | Type                 *)

  datatype Exp =			(* Expressions:               *)
    Uni   of Uni			(* U ::= L                    *)
  | Pi    of (Dec * Depend) * Exp       (*     | Pi (D, P). V         *)
                                        (*     | V1 -o V2             *)
  | With  of Exp * Exp			(*     | V1 & V2              *)
  | Top					(*     | T                    *)
  | Root  of Con * Spine		(*     | C @ S                *)
  | Redex of Exp * Spine		(*     | U @ S                *)
  | Lam   of Dec * Exp			(*     | lam D. U             *)
                                        (*     | llam D. U            *)
  | Pair  of Exp * Exp			(*     | <U1, U2>             *)
  | Unit				(*     | <>                   *)
  | EVar  of Exp option ref * Exp * Eqn list (*| X<I> : V             *)
  | EClo  of Exp * Sub			(*     | U[s]                 *)
    
  and Con =				(* Constructors:              *)
    BVar  of int			(* C ::= k                    *)
  | Const of cid			(*     | c                    *)
  | Defn  of cid			(*     | d                    *)
  | FVar  of name * Exp * Sub		(*     | F[s]                 *)
    
  and Spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | App   of Exp * Spine		(*     | U ; S                *)
  | LApp  of Exp * Spine		(*     | U ^ S                *)
  | Pi1   of Spine			(*     | pi1 S                *)
  | Pi2   of Spine			(*     | pi2 S                *)
  | SClo  of Spine * Sub		(*     | S[s]                 *)

  and Sub =				(* Explicit substitutions:    *)
    Shift of int			(* s ::= ^n                   *)
  | Dot   of Head * Sub                 (*     | H.s                  *)
  | LDot  of Head * Sub                 (*     | H^s                  *)

  and Head =				(* Heads:                     *)
    Idx of int				(* H ::= k                    *)
  | Exp of Exp * Exp			(*     | (U:V)                *)

  and Dec =				(* Declarations:              *)
    Dec of name option * Exp		(* D ::= x:V                  *)
  | LDec  of name option * Exp          (*     | x^V                  *)
    
  (* Constraint equations *)

  and Eqn =			        (* Equations                  *)
      Eqn of Exp * Exp			(* Eqn ::= (U1 == U2)         *)

  type dctx = Dec Ctx			(* G = . | G,D                *)
  type root = Con * Spine               (* R = C @ S                  *)
  type eclo = Exp * Sub   		(* Us = U[s]                  *)

  (* The global LF signature *)

  exception Error of string             (* raised if out of space     *)
  type imp = int			(* number implicit arguments  *)

  datatype Entry =			(* Signature Entry            *)
    ConstDec of name * imp		(* a : K : kind  or           *)
                * Exp * Uni	        (* c : A : type               *)
  | ConstDef of name * imp		(* a = A : K : kind  or       *)
                * Exp * Exp * Uni	(* d = M : A : type           *)
  | LinDec of name * imp * Exp * Uni    (* c ^ A : type               *)
  (* Linear Constant definition(?)  -ic *)

  fun entryName (ConstDec (name, _, _, _)) = name
    | entryName (ConstDef (name, _, _, _, _)) = name
    | entryName (LinDec   (name, _, _, _)) = name

  local
    val maxCid = Global.maxCid
    val sgnArray = Array.array (maxCid+1, ConstDec("", 0, Uni (Kind), Kind))
      : Entry Array.array
    val sgnSize  = ref(0)

  in
    (* Invariants *)
    (* All definitions are strict in all their arguments *)
    (* Definitions are stored in weak head-normal form *)
    (* if Const(cid) is a term, then sgnArray(cid) = ConstDec _ *)
    (* if Defn(cid) is a term, then sgnArray(cid) = ConstDef _ *)

    fun sgnReset () = (sgnSize := 0)
    fun sgnsize () = (!sgnSize)

    fun sgnAdd (entry) = 
        let
	  val cid = !sgnSize
	in
	  if cid > maxCid
	    then raise Error ("Global signature size "
			      ^ Int.toString (maxCid+1)
			      ^ " exceeded")
	  else (Array.update (sgnArray, cid, entry) ;
		sgnSize := cid + 1;
		cid)
	end

    (* 0 <= cid < !sgnSize *)
    fun sgnLookup (cid) = Array.sub (sgnArray, cid)
  end


  val sgnSize = sgnsize

  fun constDefn (d) =
      (case sgnLookup (d)
	 of ConstDef(_, _, U,_, _) => U)

  fun constType (c) =
      (case sgnLookup (c)
	 of ConstDec (_, _, V, _) => V
          | ConstDef (_, _, _, V, _) => V
	  | LinDec   (_, _, V, _) => V)

  fun constImp (c) =
      (case sgnLookup(c)
	 of ConstDec (_,i,_,_) => i
          | ConstDef (_,i,_,_,_) => i
	  | LinDec   (_,i,_,_) => i)

  fun constUni (c) =
      (case sgnLookup(c)
	 of ConstDec (_,_,_,L) => L
          | ConstDef (_,_,_,_,L) => L
	  | LinDec   (_,_,_,L) => L)

  (* Declaration Contexts *)

  (* ctxDec (G, k) = x:V
     Invariant: 
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)
  fun ctxDec (G, k) =
      let (* ctxDec' (G'', k') = x:V
	     where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
	fun ctxDec' (Decl (G', Dec (x, V')), 1) = Dec (x, EClo (V', Shift (k)))
	  | ctxDec' (Decl (G', LDec (x, V')), 1) =
	     LDec (x, EClo (V', Shift (k)))
	  | ctxDec' (Decl (G', _), k') = ctxDec' (G', k'-1)
	 (* ctxDec' (Null, k')  should not occur by invariant *)
      in
	ctxDec' (G, k)
      end

  (* Explicit Substitutions *)

  (* id = ^0 
  
     Invariant:
     G |- id : G        id is patsub
  *)
  val id = Shift(0)

  (* shift = ^1
  
     Invariant:
     G, V |- ^ : G       ^ is patsub
  *)
  val shift = Shift(1)

  (* bvarSub (n, s) = H'
   
     Invariant: 
     If    G |- s : G'    G' |- n : V
     then  H' = Hn         if  s = H1 .. Hn .. ^k  (.. possibly linear)
       or  H' = ^(n+k)     if  s = H1 .. Hm ^k   and m<n
     and   G |- H' : V [s]
  *)
  fun bvarSub (1, Dot(H, s)) = H
    | bvarSub (n, Dot(H, s)) = bvarSub (n-1, s)
    | bvarSub (1, LDot(H, s)) = H
    | bvarSub (n, LDot(H, s)) = bvarSub (n-1, s)
    | bvarSub (n, Shift(k))  = Idx (n+k)

  (* headSub (H, s) = H'

     Invariant:
     If   G |- s : G'     G' |- H : V
     then H' = H [s]
     and  G |- H' : V [s]
  *)
  and headSub (Idx (n), s) = bvarSub (n, s)
    | headSub (Exp (U, V), s) = Exp(EClo (U, s),V)

  (* decSub (x:V, s) = D'

     Invariant:
     If   G  |- s : G'    G' |- V : L
     then D' = x:V[s]
     and  G  |- V[s] : L
  *)
  fun decSub (Dec (x, V), s) = Dec (x, EClo (V, s))
    | decSub (LDec (x, V), s) = LDec (x, EClo (V, s))

  (* comp (s1, s2) = s'

     Invariant:
     If   G'  |- s1 : G 
     and  G'' |- s2 : G'
     then s'  = s1 o s2
     and  G'' |- s1 o s2 : G

     If  s1, s2 patsub
     then s' patsub
   *)
  fun comp (Shift (0), s) = s
    | comp (Shift (n), Dot (H, s)) = comp (Shift (n-1), s)
    | comp (Shift (n), LDot (H, s)) = comp (Shift (n-1), s) (* if implicit _ *)
    | comp (Shift (n), Shift (m)) = Shift (n+m)
    | comp (Dot (H, s), s') = Dot (headSub (H, s'), comp (s, s'))
    | comp (LDot (H, s), s') = LDot (headSub (H, s'), comp (s, s'))

  (* dot1 (s) = s'

     Invariant:
     If   G |- s : G'
     then s' = 1. (s o ^)
     and  for all V s.t.  G' |- V : L
          G, V[s] |- s' : G', V 

     If s patsub then s' patsub
   *)
  (* may be optimized by unfolding definitions *)
  (* further optimization: dot1 (id) = 1.^1 = id *)
  fun dot1 s = Dot (Idx(1), comp(s, shift))

  (* ldot1 (s) = s'

     Invariant:
     If   G |- s : G'
     then s' = 1.^ (s o ^)
     and  for all V s.t.  G' |- V : L
          G,^ V[s] |- s' : G',^ V 

     If s patsub then s' patsub
   *)
  (* may be optimized by unfolding definitions *)
  (* further optimization: ldot1 (id) = 1.^1 = id *)
  fun ldot1 s = LDot (Idx(1), comp(s, shift))

  (* EVar related functions *)

  (* newEVar (V) = newEVarCnstr (V, nil) *)
  fun newEVar (V) = EVar(ref NONE, V, nil)

  (* newEVar (V, Cnstr) = X, X new, constraints Cnstr
     If   G |- V : L
            |= Cnstr Con  (Cnstr are valid constraints, each in its own context)
     then G |- X : V
          X is the immediate successor variable to the
          variable Y indexing Cnstr
  *)
  fun newEVarCnstr (V, Cnstr) = EVar(ref NONE, V, Cnstr)

  (* newTypeVar () = X, X new
     where G |- X : type
  *)
  fun newTypeVar () = EVar(ref NONE, Uni(Type), nil)

  (* Type related functions *)

  (* targetFamList (V) = As
     As is the list of the cid's of the type family of the atomic target types
     in V
  *)
  fun targetFamList (V) =
       let
	 exception NoTargetFam
	 fun delete (b, nil) = nil
	   | delete (b, a :: As) =
	      if b = a then delete (b, As)
	      else b :: (delete (b, As))
	 fun remDuplicates (nil) = nil
	   | remDuplicates (As as a :: nil) = As
	   | remDuplicates (a :: As) = a :: remDuplicates (delete (a, As))
	 fun tgf (Root (Const(cid), _), As) = (cid :: As)
	   | tgf (Root (Defn(cid), _), As) = (cid :: As)
	   | tgf (Redex (V, S), As) = tgf (V, As)
	   | tgf (Pi(_, V), As) = tgf (V, As)
	   | tgf (With(V1,V2), As) =  tgf (V2, tgf (V1, As))
	   | tgf (Top, As) = As
	   | tgf (EVar (ref (SOME(V)), _,_), As) = tgf (V, As)
	   | tgf (EClo (V, _), As) = tgf (V, As)
	   | tgf (Lam (_, V), As) = tgf (V, As)                  (* ? -ic *)
	   | tgf (_, As) = raise NoTargetFam
             (* Unit, Pair(_, _), Root(Bvar _, _), Root(FVar _, _),
	        EVar(ref NONE,..), Uni *)
       in
	 SOME (remDuplicates (tgf (V, nil)))
	 handle NoTargetFam => NONE
       end

  (* targetFam (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     The case where V has more than one target type family is not treated. -ic
  *)
  fun targetFamOpt V =
       (case targetFamList V
	  of NONE            => NONE
	   | SOME (a :: nil) => SOME(a)
	   | _ => NONE)

  fun targetFam (V) = valOf (targetFamOpt V)

end;  (* functor IntSyn *)
