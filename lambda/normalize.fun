(* Normalization *)
(* Author: Carsten Schuermann *)

functor Normalize (structure IntSyn' : INTSYN
		   structure Whnf    : WHNF
		     sharing Whnf.IntSyn = IntSyn')
  : NORMALIZE
  (* :> NORMALIZE where IntSyn = IntSyn' *) =
struct
  structure IntSyn = IntSyn'

  local 
    structure I = IntSyn
	       
    fun normalizeExpW (U as I.Uni (L), s) = U
      | normalizeExpW (I.Pi (DP as (I.Dec _, _), U), s) = 
          I.Pi (normalizeDecP (DP, s), normalizeExp (U, I.dot1 s))
      | normalizeExpW (I.Pi (DP as (I.LDec _, _), U), s) = 
          I.Pi (normalizeDecP (DP, s), normalizeExp (U, I.ldot1 s))
      | normalizeExpW (I.With (U', U''), s) =
	  I.With (normalizeExp (U', s), normalizeExp (U'', s))
      | normalizeExpW (U as I.Root (C, S), s) = (* s = id *)
	  I.Root (C, normalizeSpine (S, s))
      | normalizeExpW (I.Top, _) = I.Top
      | normalizeExpW (I.Lam (D as I.Dec _, U), s) = 
	  I.Lam (normalizeDec (D, s), normalizeExp (U, I.dot1 s))
      | normalizeExpW (I.Lam (D as I.LDec _, U), s) = 
	  I.Lam (normalizeDec (D, s), normalizeExp (U, I.ldot1 s))
      | normalizeExpW (I.Pair (U', U''), s) =
	  I.Pair (normalizeExp (U',s), normalizeExp (U'',s))
      | normalizeExpW (I.Unit, _) = I.Unit
      | normalizeExpW (Us as (I.EVar _, s)) = I.EClo Us

    (* Invariant:
     
       normalizeExp (U, s) = U'
       If   G |- s : G' and G' |- U : V 
       then U [s] = U'
       and  U' does not contain bound EVars
    *)

    and normalizeExp Us = 
          normalizeExpW (Whnf.whnf Us)

    and normalizeSpine (I.Nil, s) = 
          I.Nil 
      | normalizeSpine (I.App (U, S), s) = 
          I.App (normalizeExp (U, s), normalizeSpine (S, s))
      | normalizeSpine (I.LApp (U, S), s) = 
          I.LApp (normalizeExp (U, s), normalizeSpine (S, s))
      | normalizeSpine (I.Pi1 S, s) = 
          I.Pi1 (normalizeSpine (S, s))
      | normalizeSpine (I.Pi2 S, s) = 
          I.Pi2 (normalizeSpine (S, s))
      | normalizeSpine (I.SClo (S, s'), s) =
	  normalizeSpine (S, I.comp (s', s))

    and normalizeDec (I.Dec (xOpt, V), s) = I.Dec (xOpt, normalizeExp (V, s))
      | normalizeDec (I.LDec (xOpt, V), s) = I.LDec (xOpt, normalizeExp (V, s))
    and normalizeDecP ((D, P), s) = (normalizeDec (D, s), P)

    and normalizeSub (s as I.Shift _) = s
      | normalizeSub (I.Dot (H as I.Idx _, s)) =
	  I.Dot (H, normalizeSub (s))
      | normalizeSub (I.Dot (I.Exp (U, V), s)) =
	  I.Dot (I.Exp (normalizeExp (U, I.id), normalizeExp (V, I.id)),
	       normalizeSub s)
      | normalizeSub (I.LDot (H as I.Idx _, s)) =
	  I.LDot (H, normalizeSub (s))
      | normalizeSub (I.LDot (I.Exp (U, V), s)) =
	  I.LDot (I.Exp (normalizeExp (U, I.id), normalizeExp (V, I.id)),
	       normalizeSub s)

    fun normalizeCtx I.Null = I.Null
      | normalizeCtx (I.Decl (G, D)) = 
          I.Decl (normalizeCtx G, normalizeDec (D, I.id))

  in
    val normalize = normalizeExp
    val normalizeDec = normalizeDec
    val normalizeCtx = normalizeCtx
  end  (* local *)
end;  (* functor Normalize *)
