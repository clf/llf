(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

functor Print (structure IntSyn' : INTSYN
		 structure Whnf : WHNF
		   sharing Whnf.IntSyn = IntSyn'
		 structure Names : NAMES
		   sharing Names.IntSyn = IntSyn'
		 structure Formatter' : FORMATTER
		 val internal : bool)
  : PRINT
  (* :> PRINT
        where IntSyn = IntSyn'
        where Formatter = Formatter'
  *) =
struct

structure IntSyn = IntSyn'
structure Formatter = Formatter'

val printDepth = ref (NONE:int option)
val printLength = ref (NONE:int option)

local
  (* some shorthands *)
  structure I = IntSyn
  structure FX = Names.Fixity
  structure F = Formatter
  val Str = F.String

  fun nameOf (SOME(id)) = id
    | nameOf (NONE) = "_"

  (* Note: Names.evarName will enter name into global table *)
  fun fmtEVar (G, X) = Str (Names.evarName(G, X))

  fun isNil (I.Nil) = true
    | isNil (I.SClo(S,_)) = isNil S
    | isNil _ = false

  (* to determine if EVar would have arguments *)
  fun isGlobal (G, I.Shift(k)) = (k = I.ctxLength G)
    | isGlobal _ = false

  (* raise EVar's to the global context *)
  (* not necessarily desirable *)
  fun subToSpine (depth, s) =
    let fun sTS (I.Shift(k), S) =
            if k < depth
	      then sTS (I.Dot (I.Idx (k+1), I.Shift(k+1)), S)
	    else (* k >= depth *) S
	  | sTS (I.Dot(I.Idx(k), s), S) =
	      sTS (s, I.App(I.Root(I.BVar(k), I.Nil), S))
	  | sTS (I.Dot(I.Exp(U, _), s), S) =
	      sTS (s, I.App(U, S))
	  | sTS (I.LDot(I.Idx(k), s), S) =
	      sTS (s, I.LApp(I.Root(I.BVar(k), I.Nil), S))
	  | sTS (I.LDot(I.Exp(U, _), s), S) =
	      sTS (s, I.LApp(U, S))
    in
      sTS (s, I.Nil)
    end 

  fun sclo' (NONE, s) = NONE
    | sclo' (SOME(S), s) = SOME(I.SClo(S,s))

  (* dropImp (i, S, n)
     = SOME(S')
       where we drop i arguments from S to obtain S', and
       S' has at least n arguments remaining
     = NONE if no such S' exists
  *)
  fun dropImp (0, S, n) =
      let fun checkArgNumber (S', 0) = SOME(S)
	    | checkArgNumber (I.Nil, n) = NONE
	    | checkArgNumber (I.App(U,S'), n) =
		checkArgNumber (S', n-1)
	    | checkArgNumber (I.LApp(U,S'), n) = NONE   (* No linear infix's *)
	    | checkArgNumber (I.Pi1 _, _) = NONE
	    | checkArgNumber (I.Pi2 _, _) = NONE
	    | checkArgNumber (I.SClo(S', s), n) =
		checkArgNumber (S', n)
      in
	checkArgNumber (S, n)
      end
    | dropImp (i, I.App(U,S), n) = dropImp (i-1, S, n)
    | dropImp (i, I.LApp _, _) = NONE
    | dropImp (i, I.Pi1 _, _) = NONE
    | dropImp (i, I.Pi2 _, _) = NONE
    | dropImp (i, I.SClo(S,s), n) = 
	sclo' (dropImp (i, S, n), s)
    | dropImp (i, I.Nil, n) = NONE

  fun exceeded (_,NONE) = false
    | exceeded (n:int,SOME(m:int)) = (n >= m)

  datatype ctxt = Ctxt of FX.fixity * F.format list * int
  datatype opargs =
      OpArgs of FX.fixity * F.format list * I.Spine
    | EtaLong of I.Exp

  val noCtxt = Ctxt (FX.Prefix(FX.ctxPrec), [], 0)

  val projFix = FX.Prefix (FX.projPrec)
  val juxFix = FX.Infix (FX.appPrec, FX.Left)

  fun witH (V1, V2) =
	 OpArgs(FX.Infix(FX.withPrec, FX.Right),
		[F.Break, Str "&", F.Space],
		I.App (V1, I.App(V2, I.Nil)))

  fun arrow (V1, V2) =
	 OpArgs(FX.Infix(FX.arrowPrec, FX.Right),
		[F.Break, Str "->", F.Space],
		I.App (V1, I.App(V2, I.Nil)))

  fun linArrow (V1, V2) =
	 OpArgs(FX.Infix(FX.arrowPrec, FX.Right),
		[F.Break, Str "-o", F.Space],
		I.App (V1, I.App(V2, I.Nil)))

  fun pair (V1, V2) =
	 OpArgs(FX.Infix(FX.pairPrec, FX.Right),
		[F.Space, Str ",", F.Break],
		I.App (V1, I.App(V2, I.Nil)))

  (* Nonfix corresponds to application = maximal precedence *)
  val appCtxt = Ctxt (FX.Nonfix, [], 0)

  fun fixityCon (I.Const(cid)) = Names.getFixity (cid)
    | fixityCon (I.Defn(cid)) = Names.getFixity (cid)
    | fixityCon _ = FX.Nonfix (* BVar, FVar *)

  fun impCon (I.Const(cid)) = I.constImp (cid)
    | impCon (I.Defn(cid)) = I.constImp (cid)
    | impCon _ = 0			(* BVar, FVar *)

  fun argNumber (FX.Nonfix) = 0
    | argNumber (FX.Infix _) = 2
    | argNumber (FX.Prefix _) = 1
    | argNumber (FX.Postfix _) = 1

  fun fmtCon (G, I.BVar(n)) = Str (Names.bvarName(G, n))
    | fmtCon (G, I.Const(cid)) = Str (Names.constName (cid))
    | fmtCon (G, I.Defn(cid)) = Str (Names.constName (cid))
    | fmtCon (G, I.FVar (name, _, _)) = Str ("`" ^ name)

  (* for internal printing *)
  fun opargsInternal (G, (C,S)) = OpArgs (FX.Nonfix, [fmtCon(G,C)], S)

  (* for external printing *)
  fun opargsExternal (G, R as (C,S)) =
      let
	val opFmt = fmtCon (G, C)
	val fixity = fixityCon C
	fun oe (SOME(S')) =
	    (case fixity
	       of FX.Nonfix => OpArgs (FX.Nonfix, [opFmt], S')
	        | FX.Prefix _ => OpArgs (fixity, [opFmt, F.Break], S')
		| FX.Postfix _ => OpArgs (fixity, [F.Break, opFmt], S')
		| FX.Infix _ => OpArgs (fixity, [F.Break, opFmt, F.Space], S'))
	  | oe NONE = EtaLong (Whnf.etaExpandRoot (I.Root R))
      in
	oe (dropImp (impCon C, S, argNumber fixity))
      end

  val opargs = if internal then opargsInternal else opargsExternal

  (* evarArgs: make local parameters up to depth d explicit as arguments to X *)
  (* if d = I.ctxLength (G) all parameters are made explicit *)
  fun evarArgs (G, d, X, s) =
      OpArgs (FX.Nonfix, [fmtEVar(G, X)],
	      subToSpine (I.ctxLength(G), s))

  (* implicit arguments have been elided (infix operators) *)
  fun fst (I.App (U1, _), s) = (U1, s)
    | fst (I.SClo (S, s'), s) = fst (S, I.comp (s', s))

  fun snd (I.App (U1, S), s) = fst (S, s)
    | snd (I.SClo (S, s'), s) = snd (S, I.comp (s', s))

  fun elide (l) = case !printLength
		     of NONE => false
		      | SOME(l') => (l > l')

  val ldots = Str "..."
  fun addots (l) = case !printLength
		     of NONE => false
		      | SOME(l') => (l = l')

  fun parens ((fixity', fixity), fmt) =
      if FX.prec(fixity') >= FX.prec(fixity)
	then F.Hbox [Str "(", fmt, Str ")"]
      else fmt

  fun eqFix (FX.Infix(p,FX.Left), FX.Infix(p',FX.Left)) = (p = p')
    | eqFix (FX.Infix(p,FX.Right), FX.Infix(p', FX.Right)) = (p = p')
      (* Infix(_,None) should never be asked *)
    | eqFix (FX.Prefix(p), FX.Prefix(p')) = (p = p')
    | eqFix (FX.Postfix(p), FX.Postfix(p')) = (p = p')
      (* Nonfix should never be asked *)
    | eqFix _ = false

  fun addAccum (fmt, _, nil) = fmt
    | addAccum (fmt, FX.Infix(_, FX.Left), accum) = F.HVbox ([fmt] @ accum)
    | addAccum (fmt, FX.Infix(_, FX.Right), accum) = F.HVbox (accum @ [fmt])  (* Expense! *)
    | addAccum (fmt, FX.Prefix _, accum) = F.HVbox (accum @ [fmt])
    | addAccum (fmt, FX.Postfix _, accum) = F.HVbox ([fmt] @ accum)
    (* FX.Infix(None,_), FX.Nonfix should never arise *)

  fun aa (Ctxt (fixity, accum, l), fmt) = addAccum (fmt, fixity, accum)

  fun fmtUni (I.Type) = Str "type"
    | fmtUni (I.Kind) = Str "kind"   (* impossible *)

  fun fmtExpW (G, d, ctx, (I.Uni(L), s)) = aa (ctx, fmtUni(L))
    | fmtExpW (G, d, ctx, (I.Pi((D as I.Dec(_,V1),P),V2), s)) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
	 of I.Maybe => let
			 val D' = Names.decName (G, D)
		       in
			 fmtLevel (I.Decl (G, D'), (* I.decSub (D', s) *)
				   d, ctx, (braces (G, d, ((D',V2), s)),
					    I.dot1 s))
		       end
	  | I.No => fmtLevel (I.Decl (G, D), (* I.decSub (D, s) *)
			      d, ctx, (arrow(I.EClo(V1,I.shift), V2), I.dot1 s)))
    | fmtExpW (G, d, ctx, (I.Pi((D as I.LDec(_,V1),_),V2), s)) =  (* P=No *)
	fmtLevel (I.Decl (G, D), (* I.decSub (D, s) *)
		  d, ctx, (linArrow(I.EClo(V1,I.shift), V2), I.ldot1 s))
    | fmtExpW (G, d, ctx, (I.With(V1,V2), s)) =
	fmtLevel (G, d, ctx, (witH(V1,V2), s))
    | fmtExpW (G, d, ctx, (I.Top, s)) = Str "<T>"
    | fmtExpW (G, d, ctx, (U as I.Root(R as (C,_)), s)) =
	 fmtOpArgs (G, d, ctx, opargs (G, R), s)
    (* I.Redex not possible *)
    | fmtExpW (G, d, ctx, (I.Lam(D, U), s)) = 
      let
	val D' = Names.decName (G, D)
      in
	fmtLevel (I.Decl (G, D'), (* I.decSub (D', s) *)
		  d, ctx, (brackets (G, d, ((D', U), s)), I.dot1 s))
      end
    | fmtExpW (G, d, ctx, (I.Pair(V1,V2), s)) =
	fmtLevel (G, d, ctx, (pair(V1,V2), s))
    | fmtExpW (G, d, ctx, (I.Unit, s)) = Str "()"
    | fmtExpW (G, d, ctx, (X as I.EVar _, s)) =
      (* assume dereferenced during whnf *)
      if internal then aa (ctx, F.HVbox (fmtEVar(G,X)::fmtSub(G,d,s)))
      else fmtOpArgs (G, d, ctx, evarArgs (G, d, X, s), I.id)
    (* I.EClo not possible for Whnf *)

  and fmtOpArgs (G, d, ctx, oa as OpArgs(_, opFmts, S'), s) =
      if isNil S'
	then aa (ctx, List.hd opFmts)	(* opFmts = [fmtCon(G,C)] *)
      else fmtLevel (G, d, ctx, (oa, s))
    | fmtOpArgs (G, d, ctx, EtaLong(U'), s) =
	fmtExpW (G, d, ctx, (U', s))

  and fmtSub (G, d, s) = Str "[" :: fmtSub' (G, d, 0, s)
  and fmtSub' (G, d, l, s) = if elide l then [ldots] else fmtSub'' (G, d, l, s)
  and fmtSub'' (G, d, l, I.Shift(k)) = [Str ("|" ^ Int.toString k), Str "]"]
    | fmtSub'' (G, d, l, I.Dot(I.Idx(k), s)) =
        Str (Names.bvarName (G, k)) :: Str "." :: F.Break
	:: fmtSub' (G, d, l+1, s)
    | fmtSub'' (G, d, l, I.Dot(I.Exp(U,_), s)) =
	fmtExp (G, d+1, noCtxt, (U, I.id))
	:: Str "." :: F.Break :: fmtSub' (G, d, l+1, s)
    | fmtSub'' (G, d, l, I.LDot(I.Idx(k), s)) =
        Str (Names.bvarName (G, k)) :: Str "^" :: F.Break
	:: fmtSub' (G, d, l+1, s)
    | fmtSub'' (G, d, l, I.LDot(I.Exp(U,_), s)) =
	fmtExp (G, d+1, noCtxt, (U, I.id))
	:: Str "^" :: F.Break :: fmtSub' (G, d, l+1, s)

  and fmtExp (G, d, ctx, (U, s)) =
	 if exceeded(d,!printDepth)
	    then Str "%%"
	    else fmtExpW (G, d, ctx, Whnf.whnf (U, s))

  and fmtSpine (G, d, l, fmts, lastFix, (I.Nil, _)) = fmts
    | fmtSpine (G, d, l, fmts, lastFix, (I.SClo (S, s'), s)) =
       fmtSpine (G, d, l, fmts, lastFix, (S, I.comp(s',s)))
    | fmtSpine (G, d, l, fmts, lastFix, (I.App(U, S), s)) =
       if elide (l) then fmts		(* necessary? *)
       else if addots (l) then fmts @ [ldots]
       else fmtSpine (G, d, l+1,
		      fmts @ [F.Break, fmtExp (G, d+1, appCtxt, (U, s))],
		      juxFix, (S, s))
    | fmtSpine (G, d, l, fmts, lastFix, (I.LApp(U, S), s)) =
       fmtSpine (G, d, l+1,
		 fmts @ [F.Space, Str "^", F.Break,
			 fmtExp (G, d+1, appCtxt, (U, s))],   (* ? -ic *)
		 juxFix, (S, s))
    | fmtSpine (G, d, l, fmts, lastFix, (I.Pi1 S, s)) =
       fmtSpine (G, d, l+1,
		 [Str "<fst>", F.Space,
		  parens ((projFix,lastFix), F.HVbox (fmts))],
		 projFix, (S, s))
    | fmtSpine (G, d, l, fmts, lastFix, (I.Pi2 S, s)) =
       fmtSpine (G, d, l+1,
		 [Str "<snd>", F.Space,
		  parens ((projFix,lastFix), F.HVbox (fmts))],
		 projFix, (S, s))

(*  and fmtSpine' (G, d, l, (I.Nil, _)) = []                   -ic
    | fmtSpine' (G, d, l, (I.SClo (S, s'), s)) =
        fmtSpine' (G, d, l, (S, I.comp(s', s)))
    | fmtSpine' (G, d, l, (S, s)) =
	F.Break :: fmtSpine (G, d, l+1, (S, s)) *)

  and fmtLevel (G, d, Ctxt (fixity', accum, l),
		(OpArgs (fixity as FX.Nonfix, fmts, S), s)) =
      let
	val atm = fmtSpine (G, d, 0, fmts, projFix, (S,s))
      in
	(* F.HVbox doesn't work if last item of HVbox is F.Break *)
	addAccum (parens ((fixity',fixity), F.HVbox (atm)),
		  fixity', accum)
        (* possible improvement along the following lines: *)
	(*
	   if (#2 (F.Width (F.Hbox (fmts)))) < 4
	   then F.Hbox [F.Hbox(fmts), F.HVbox0 1 1 1 atm]
	   else ...
        *)
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
		(OpArgs (fixity as (FX.Infix(p, FX.Left)), fmts, S), s)) =
      let val accMore = eqFix (fixity, fixity')
	val rhs = if accMore andalso elide(l) then []
		  else if accMore andalso addots(l) then fmts @ [ldots]
		       else fmts @ [fmtExp (G, d+1, Ctxt (FX.Infix(p,FX.None),nil,0),
					    snd (S, s))]
      in
	if accMore
	  then fmtExp (G, d, Ctxt (fixity, rhs @ accum, l+1), fst (S, s))
	else let
	       val both = fmtExp (G, d, Ctxt (fixity, rhs, 0), fst (S, s))
	     in
	       addAccum (parens ((fixity',fixity), both), fixity', accum)
	     end
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
		(OpArgs (fixity as FX.Infix(p, FX.Right), fmts, S), s)) =
      let
	  val accMore = eqFix (fixity, fixity')
	  val lhs = if accMore andalso elide(l) then []
		    else if accMore andalso addots(l) then [ldots] @ fmts
			 else [fmtExp (G, d+1, Ctxt (FX.Infix(p,FX.None),nil,0), fst(S, s))] @ fmts
      in
	if accMore
	  then fmtExp (G, d, Ctxt (fixity, accum @ lhs, l+1), snd (S, s))
	else let
	       val both = fmtExp (G, d, Ctxt (fixity, lhs, 0), snd (S, s))
	     in
	       addAccum (parens ((fixity', fixity), both), fixity', accum)
	     end
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
		(OpArgs(fixity as (FX.Infix(_,FX.None)), fmts, S), s)) =
      let
	  val lhs = fmtExp (G, d+1, Ctxt (fixity, nil, 0), fst(S, s))
	  val rhs = fmtExp (G, d+1, Ctxt (fixity, nil, 0), snd(S, s))
      in
	addAccum (parens ((fixity',fixity),
			  F.HVbox ([lhs] @ fmts @ [rhs])), fixity', accum)
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
		(OpArgs (fixity as (FX.Prefix _), fmts, S), s)) =
      let
	  val accMore = eqFix (fixity', fixity)
	  val pfx = if accMore andalso elide(l) then []
		    else if accMore andalso addots(l) then [ldots, F.Break]
			 else fmts
      in
	if accMore
	  then fmtExp (G, d, Ctxt (fixity, accum @ pfx, l+1), fst(S, s))
	else let
	       val whole = fmtExp (G, d, Ctxt (fixity, pfx, 0), fst (S, s))
	     in
	       addAccum (parens ((fixity',fixity), whole), fixity', accum)
	     end
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
		(OpArgs (fixity as (FX.Postfix _), fmts, S), s)) =
      let
	  val accMore = eqFix (fixity', fixity)
	  val pfx = if accMore andalso elide(l) then []
		    else if accMore andalso addots(l) then [F.Break, ldots]
			 else fmts
      in
	if accMore
	  then fmtExp (G, d, Ctxt (fixity, pfx @ accum, l+1), fst(S, s))
	else let
	       val whole = fmtExp (G, d, Ctxt (fixity, pfx, 0), fst (S, s))
	     in
	       addAccum (parens ((fixity', fixity), whole), fixity', accum)
	     end
      end

  and braces (G, d, ((D,V), s)) =
	 OpArgs(FX.Prefix(FX.piPrec),
		[Str "{" , fmtDec (G, d, (D,s)), Str "}", F.Break],
		IntSyn.App(V, IntSyn.Nil))

  and brackets (G, d, ((D,U), s)) =
	 OpArgs(FX.Prefix(FX.absPrec),
		[Str "[" , fmtDec (G, d, (D,s)), Str "]", F.Break],
		IntSyn.App(U, IntSyn.Nil))

  and fmtDec (G, d, (I.Dec (x, V), s)) =
      F.HVbox [Str (nameOf (x)), Str ":", fmtExp (G, d+1, noCtxt, (V,s))]
      (* alternative with more whitespace *)
      (* F.HVbox [Str (nameOf (x)), F.Space, Str ":", F.Break, fmtExp (G, d+1, noCtxt, (V,s))] *)
    | fmtDec (G, d, (I.LDec (x, V), s)) =
      F.HVbox [Str (nameOf (x)), Str "^", fmtExp (G, d+1, noCtxt, (V,s))]

  fun fmtEntry (I.ConstDec (name, _, V, L)) =
      F.Hbox [Str(name), F.Space, Str ":", F.Break,
	      fmtExp (I.Null, 0, noCtxt, (V, I.id)), Str "."]
    | fmtEntry (I.ConstDef (name, _, U, V, L)) =
      (* print the type of definitions? *)
      (* should coordinate variable names between type and definition *)
      F.HVbox [Str(name), F.Space, Str ":", F.Break,
	       fmtExp (I.Null, 0, noCtxt, (V, I.id)), F.Break,
	       Str "=", F.Space,
	       fmtExp (I.Null, 0, noCtxt, (U, I.id)), Str "."]
    | fmtEntry (I.LinDec (name, _, V, L)) =
      F.Hbox [Str(name), F.Space, Str "^", F.Break,
	      fmtExp (I.Null, 0, noCtxt, (V, I.id)), Str "."]

in

  fun formatDec (G, D) = fmtDec (G, 0, (D, I.id))
  fun formatExp (G, U) = fmtExp (G, 0, noCtxt, (U, I.id))
  fun formatEntry (e) = fmtEntry (e)

  fun decToString (G, D) = F.makestring_fmt (formatDec (G, D))
  fun expToString (G, U) = F.makestring_fmt (formatExp (G, U))
  fun entryToString (e) =
      (Names.varReset ();
       F.makestring_fmt (formatEntry (e)))

  fun fmtNamedEVar (U,name) =
        F.HVbox [Str name, F.Space, Str "=", F.Break, formatExp (I.Null, U)]

  fun fmtEVarInst (nil) = [Str "Empty Substitution"]
    | fmtEVarInst ((U,name)::nil) = [fmtNamedEVar (U, name)]
    | fmtEVarInst ((U,name)::Xs) =
        fmtNamedEVar (U, name) :: Str ";" :: F.Break :: fmtEVarInst Xs

  fun evarInstToString Xs =
       F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (fmtEVarInst Xs), Str "."])

end  (* local ... *)

end  (* functor Print *)
