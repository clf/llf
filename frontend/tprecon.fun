(* Type Reconstruction *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

functor TpRecon (structure Global : GLOBAL
		 structure IntSyn' : INTSYN
		 structure Names : NAMES
		   sharing Names.IntSyn = IntSyn'
		 structure Paths' : PATHS
		 structure Whnf : WHNF
		   sharing Whnf.IntSyn = IntSyn'
		 structure Normalize : NORMALIZE
		   sharing Normalize.IntSyn = IntSyn'
		 structure Pattern : PATTERN
		   sharing Pattern.IntSyn = IntSyn'
		 structure Unify : UNIFY
		   sharing Unify.IntSyn = IntSyn'
		 structure Abstract : ABSTRACT
		   sharing Abstract.IntSyn = IntSyn'
		 structure TypeCheck : TYPECHECK
		   sharing TypeCheck.IntSyn = IntSyn'
		 structure LinCheck : LINCHECK
		   sharing LinCheck.IntSyn = IntSyn'
		   sharing LinCheck.Paths = Paths'
		 structure Strictness : STRICTNESS
		   sharing Strictness.IntSyn = IntSyn'
		 structure IPrint : PRINT
		   sharing IPrint.IntSyn = IntSyn'
		 structure EPrint : PRINT
		   sharing EPrint.IntSyn = IntSyn'
		 structure Timers : TIMERS
                 structure Vars : VARS 
                   sharing Vars.IntSyn = IntSyn')
  : TP_RECON
  (* :> TP_RECON
        where IntSyn = IntSyn'
        where Paths = Paths'
  *) =
struct

  structure IntSyn = IntSyn'
  structure Paths = Paths'
  structure F = EPrint.Formatter
  type name = string

  (* doubleCheck = ref true
     means to re-typecheck each entry after reconstruction
  *)
  val doubleCheck = ref false

  (* Implementation of term and decl which are abstract in the parser.
     We write tm : term for the representation of a term tm and tm* :
     exp for its translation in internal syntax and d : decl for the
     representation of a declaration and d* : dec for its translation
     into internal syntax.

     We write tm* @@ S for the result of appending spine S to the
     translation of tm.

     Invariants: If    tm (G, SS) = ((U, V), oc)
                 and   G |- tm* : tp*

                 then  G |- U : V  and  G |- V : L
                 and   ((S, V), os) = SS tp*
                 and   U = tm* @@ S

                 where oc = occurrence tree associated with U
                       os = occurrence spine associated with S

     raises exception Error if such a tp* does not exist
  *)
  type term = IntSyn.dctx * (IntSyn.Exp -> (IntSyn.Spine * IntSyn.Exp) * Paths.occSpine)
                -> (IntSyn.Exp * IntSyn.Exp) * Paths.occExp
  type decl = IntSyn.dctx -> IntSyn.Dec * Paths.occExp option	(* must be x:A where A:type *)

  (* Various error-related functions *)

  exception Error of string
  fun error (r, msg) =
      raise Error (Paths.toString r ^ " " ^ "Error: " ^ msg)

  fun joinRegions (oc1, oc2) =
        Paths.join (Paths.toRegion oc1, Paths.toRegion oc2)

  fun mismatchError (G, (V1', s), ((U2, V2), oc2), msg) =
      let
	val r = Paths.toRegion oc2
	val V1'fmt = EPrint.formatExp (G, IntSyn.EClo (V1', s))
	val V2fmt = EPrint.formatExp (G, V2)
	val diff = F.Vbox0 0 1
	           [F.String "Expected:", F.Space, V1'fmt, F.Break,
		    F.String "Found:   ", F.Space, V2fmt]
      in
	error (r, "Type mismatch\n"
	           ^ F.makestring_fmt diff ^ "\n"
	           ^ msg ^ "\n")
      end

  fun hasTypeError (G, (V1, oc1), (V2, oc2), msg) =
      let
	val r2 = Paths.toRegion oc2
	val V1fmt = EPrint.formatExp (G, V1)
	val V2fmt = EPrint.formatExp (G, V2)
	val diff = F.Vbox0 0 1
	           [F.String "Synthesized: ", V1fmt, F.Break,
		    F.String "Ascribed:    ", V2fmt]
      in
	error (r2, "Type ascription error\n"
	           ^ F.makestring_fmt diff ^ "\n"
	           ^ msg ^ "\n")
      end

  fun extraneousError (G, (V1, s), (U2, oc2)) =
      let
	val V1fmt = EPrint.formatExp (G, IntSyn.EClo (V1, s))
	val nonFun = F.HVbox [F.Space, V1fmt, F.Break,
			      F.String "is not an intuitionistic function type"]
	val r2 = Paths.toRegion oc2
      in
        error (r2, "Extraneous argument\n" ^ F.makestring_fmt nonFun ^ "\n")
      end

  fun extraneousError' (G, (V1, s), (U2, oc2)) =
      let
	val V1fmt = EPrint.formatExp (G, IntSyn.EClo (V1, s))
	val nonFun = F.HVbox [F.Space, V1fmt, F.Break,
			      F.String "is not a linear function type"]
	val r2 = Paths.toRegion oc2
      in
        error (r2, "Extraneous argument\n" ^ F.makestring_fmt nonFun ^ "\n")
      end

  fun linearFunError (G, (V1, s), (U2, oc2)) =
      let
	val V1fmt = EPrint.formatExp (G, IntSyn.EClo (V1, s))
	val nonFun = F.HVbox [F.Space, V1fmt, F.Break,
		      F.String "is not an intuitionistic function type"]
	val r2 = Paths.toRegion oc2
      in
        error (r2, "Linear application expected:\n" ^
	           F.makestring_fmt nonFun ^ "\n")
      end

  fun extraneousProjError (G, (V1, s)) =
      let
	val V1fmt = EPrint.formatExp (G, IntSyn.EClo (V1, s))
	val nonPair = F.HVbox [F.Space, V1fmt, F.Break,
			      F.String "is not a product type"]
      in
        raise Error ("Error" ^ F.makestring_fmt nonPair ^ "\n")
      end

  (* nilSS --- empty spine and occurrence tree *)
  fun nilSS (V) = ((IntSyn.Nil, V), Paths.nils)

  (* Checking universe level restrictions *)
  fun checkUni (L, r) =
      (case Whnf.whnf (L, IntSyn.id)
	 of (IntSyn.Uni(_), _) => ()
	  | _ => error (r, "Classifier is not a type or kind"))

  fun getUni (L, r) =
      (case Whnf.whnf (L, IntSyn.id)
	 of (IntSyn.Uni (level), _) => level
          | _ => error (r, "Classifier is not a type or kind"))

  fun checkType (L, r) =
      (case Whnf.whnf (L, IntSyn.id)
         of (IntSyn.Uni (IntSyn.Type), _) => ()
          | _ => error (r, "Classifier is not a type"))

  (* Resolving identifier names *)
  fun findConst (name) =
      (case Names.nameLookup (name)
	 of NONE => NONE
          | SOME(cid) =>
	     (case IntSyn.sgnLookup(cid)
		of IntSyn.ConstDec (_, imp, V, _) =>
		     SOME(IntSyn.Const(cid), imp, V)
	         | IntSyn.ConstDef (_, imp, _, V, _) =>
		     SOME(IntSyn.Defn(cid), imp, V)
		 | IntSyn.LinDec (_, imp, V, _) =>
		     SOME(IntSyn.Const(cid), imp, V)))

  fun findName (name, G) =
      let fun findName' (IntSyn.Null, k) = NONE
	    | findName' (IntSyn.Decl (G', IntSyn.Dec(NONE, _)), k) =
	        findName' (G', k+1)
            | findName' (IntSyn.Decl (G', IntSyn.Dec(SOME(name'), V')), k) =
	      if name = name'
		then SOME(IntSyn.BVar(k),IntSyn.EClo(V',IntSyn.Shift(k)))
	      else findName' (G', k+1)
	    | findName' (IntSyn.Decl (G', IntSyn.LDec(NONE, _)), k) =
	        findName' (G', k+1)
            | findName' (IntSyn.Decl (G', IntSyn.LDec(SOME(name'), V')), k) =
	      if name = name'
		then SOME(IntSyn.BVar(k),IntSyn.EClo(V',IntSyn.Shift(k)))
	      else findName' (G', k+1)
      in
	findName' (G, 1)
      end

  (* Translating identifiers, once they have been classified into *)
  (* Constants, BVars or FVars *)
  fun const ((c,i,V'), r, SS) =
      let
	fun supplyImplicit (0, (V', s)) = SS (IntSyn.EClo(V', s))
	  | supplyImplicit (i, (IntSyn.Pi ((IntSyn.Dec (x, V1), _), V2), s)) =
	    let
	      val U1 = IntSyn.newEVar (IntSyn.EClo(V1, s))
	      val ((S2, V), os) = supplyImplicit (i-1,
                              Whnf.whnf (V2, IntSyn.Dot(IntSyn.Exp(U1,V1), s)))
	    in
	      ((IntSyn.App (U1, S2), V), os)
	    end
	val ((S, V), os) = supplyImplicit (i, Whnf.whnf (V', IntSyn.id))
      in
	((IntSyn.Root (c, S), V),
	 Paths.root (Paths.toRegionSpine (os, r), Paths.leaf r, i, os))
      end

  fun bvar ((n, V'), r, SS) =
      let
	val ((S, V), os) = SS V'
      in
	((IntSyn.Root (n, S), V),
	 Paths.root (Paths.toRegionSpine (os, r), Paths.leaf r, 0, os))
      end

  fun var (name, r, depth, SS) =
      let
        val (V', H) = Vars.var (name, depth)
	val ((S, V), os) = SS V'
      in
	((H S, V),
	 Paths.root (Paths.toRegionSpine (os, r), Paths.leaf r, 0, os))
      end

  (* The remaining functions appear in the interface *)
  (* Resolving lower-case, upper-case or quoted identifiers *)
  fun lcid (name, r) (G, SS) =
      (case findName (name, G)
	 of NONE => (case findConst (name)
		       of NONE => error (r, "Undeclared constant " ^ name)
			| SOME info => (const (info, r, SS)))
          | SOME nV => bvar (nV, r, SS))

  fun ucid (name, r) (G, SS) =
      (case findName (name, G)
	 of NONE => (case findConst (name)
		       of NONE => var (name, r, IntSyn.ctxLength G, SS)
			| SOME info => const (info, r, SS))
	  | SOME nV => bvar (nV, r, SS))

  (* currently not used *)
  fun quid (name,r) (G, SS) =
      (case findConst (name)
	 of NONE => error (r, "Undeclared quoted constant " ^ name)
	  | SOME info => const (info, r, SS))

  (* Application *)
  fun app (tm1, tm2) (G, SS) =
        (* argument first or function first? *)
        tm1 (G, fn V1 => app2 (tm2) (G, SS) (V1))

  and app2 (tm2) (G, SS) (V1) =
         (* convert tm2 early to obtain error location *)
         app2' (tm2 (G, nilSS)) (G, SS) (V1)

  and app2' (UV2 as ((U2, V2), oc2)) (G, SS) (V1) =
      (case Whnf.whnf (V1, IntSyn.id)
	 of (IntSyn.Pi ((IntSyn.Dec (x, V1'), P), V1''), s) =>
	    let
	      val _ = Unify.unify ((V1', s), (V2, IntSyn.id))
		      handle Unify.Unify(msg) => mismatchError (G, (V1', s), UV2, msg)
	      val ((S, V), os) = SS (IntSyn.EClo (V1'', Pattern.dotEta (IntSyn.Exp(U2,V1'), s)))
	    in
	      ((IntSyn.App (U2, S), V), Paths.app (oc2, os))
	    end
	  | (V1 as IntSyn.Pi ((IntSyn.LDec (x, V1'), P), V1''), s) =>
	      (linearFunError (G, (V1, s), (U2, oc2));
	       ((IntSyn.Nil, IntSyn.Top), Paths.nils)) (* dead code-nonsense *)
          | (V1, s) =>
	    let
	      val V1' = IntSyn.newTypeVar ()
	      val V1'' = IntSyn.newTypeVar ()
	      (* Invariant: type families are always constants and *)
	      (* therefore of known kind.  In case tm1 is a type family *)
	      (* the other case (V1 = Pi x:A. K) applies *)
	      val V = IntSyn.Pi ((IntSyn.Dec (NONE, V1'), IntSyn.Maybe), V1'')
	    in
	      Unify.unify ((V1, s), (V, IntSyn.id))
	      handle Unify.Unify (msg) =>
		extraneousError (G, (V1, s), (U2, oc2));
	      (* now, first case must apply *)
	      app2' (UV2) (G, SS) (V)
	    end)

  (* Linear application *)
  fun linapp (tm1, tm2) (G, SS) =
        (* argument first or function first? *)
        tm1 (G, fn V1 => linapp2 (tm2) (G, SS) (V1))

  and linapp2 (tm2) (G, SS) (V1) =
         (* convert tm2 early to obtain error location *)
         linapp2' (tm2 (G, nilSS)) (G, SS) (V1)

  and linapp2' (UV2 as ((U2, V2), oc2)) (G, SS) (V1) =
      (case Whnf.whnf (V1, IntSyn.id)
	 of (IntSyn.Pi ((IntSyn.LDec (x, V1'), _), V1''), s) =>
	    let
	      val _ = Unify.unify ((V1', s), (V2, IntSyn.id))
		      handle Unify.Unify(msg) =>
			mismatchError (G, (V1', s), UV2, msg)
	      val ((S, V), os) = SS (IntSyn.EClo (V1'', Pattern.ldotEta (IntSyn.Exp(U2,V1'), s)))
	    in
	      ((IntSyn.LApp (U2, S), V), Paths.app (oc2, os))
	    end
	  | (V1, s) =>
	    let
	      val V1' = IntSyn.newTypeVar ()
	      val V1'' = IntSyn.newTypeVar ()
	      (* Invariant: type families are always constants and *)
	      (* therefore of known kind.  In case tm1 is a type family *)
	      (* the other case (V1 = Pi x:A. K) applies *)
	      val V = IntSyn.Pi ((IntSyn.LDec (NONE, V1'), IntSyn.No), V1'')
	    in
	      Unify.unify ((V1, s), (V, IntSyn.id))
	      handle Unify.Unify (msg) =>
		extraneousError' (G, (V1, s), (U2, oc2));
	      (* now, first case must apply *)
	      linapp2' (UV2) (G, SS) (V)
	    end)

  (* First projection *)
  fun first (tm) (G, SS) =
       tm (G, fn V1 => first' (G, SS) (V1))
  and first' (G, SS) (V1) =
       (case Whnf.whnf (V1, IntSyn.id)
	  of (IntSyn.With (V1', _), s) =>
	       let
		 val ((S, V2), os) = SS V1'  (* unify V1 and V2? -ic *)
	       in
		 ((IntSyn.Pi1 S, V2), Paths.proj os)
	       end
           | (V, s) =>
	       let
		 val V1' = IntSyn.newTypeVar ()
		 val V1'' = IntSyn.newTypeVar ()
		 val V2 = IntSyn.With (V1', V1'')
	       in
		 Unify.unify ((V, s), (V2, IntSyn.id))
		   handle Unify.Unify (msg) =>
		     extraneousProjError (G, (V, s));  (* location is missing! -ic *)
		   (* now, first case must apply *)
		   first' (G, SS) (V2)
	       end)

  (* Second projection *)
  fun second (tm) (G, SS) =
       tm (G, fn V1 => second' (G, SS) (V1))
  and second' (G, SS) (V1) =
       (case Whnf.whnf (V1, IntSyn.id)
	  of (IntSyn.With (_, V1''), s) =>
	       let
		 val ((S, V2), os) = SS V1''  (* unify V1 and V2? -ic *)
	       in
		 ((IntSyn.Pi2 S, V2), Paths.proj os)
	       end
           | (V, s) =>
	       let
		 val V1' = IntSyn.newTypeVar ()
		 val V1'' = IntSyn.newTypeVar ()
		 val V2 = IntSyn.With (V1', V1'')
	       in
		 Unify.unify ((V, s), (V2, IntSyn.id))
		   handle Unify.Unify (msg) =>
		     extraneousProjError (G, (V, s));  (* location is missing! -ic *)
		   (* now, first case must apply *)
		   second' (G, SS) (V2)
	       end)

  (* Non-dependent function types *)
  fun arrow (tm1, tm2) (G, SS) =
      let
	val ((V1, L1), oc1) = tm1 (G, nilSS)
	val _ = checkType (L1, Paths.toRegion oc1)
	val D1 = IntSyn.Dec (NONE, V1)
	val ((V2, L2), oc2) = tm2 (G, nilSS)
	val _ = checkUni (L2, Paths.toRegion oc2)
	val r = joinRegions (oc1, oc2)
      in
	case SS L2
	  of ((IntSyn.Nil, L2'), _) =>
	      ((IntSyn.Pi ((D1, IntSyn.No), IntSyn.EClo(V2,IntSyn.shift)), L2),
	       Paths.bind (r, SOME(oc1), oc2))
	   (* can the next case arise? *)
	   | ((S, V'), _) => error (r, "function type applied to argument")
      end

  fun backarrow (tm2, tm1) (G, SS) =
        arrow (tm1, tm2) (G, SS)

  (* Linear function types *)
  fun lolli (tm1, tm2) (G, SS) =
      let
	val ((V1, L1), oc1) = tm1 (G, nilSS)
	val _ = checkType (L1, Paths.toRegion oc1)
	val D1 = IntSyn.LDec (NONE, V1)
	val ((V2, L2), oc2) = tm2 (G, nilSS)
	val _ = checkUni (L2, Paths.toRegion oc2)
	val r = joinRegions (oc1, oc2)
      in
	case SS L2
	  of ((IntSyn.Nil, L2'), _) =>
	      ((IntSyn.Pi ((D1, IntSyn.No), IntSyn.EClo(V2,IntSyn.shift)), L2),
	       Paths.bind (r, SOME(oc1), oc2))
	   (* can the next case arise? *)
	   | ((S, V'), _) =>
	      error (r, "linear function type applied to argument")
      end

  fun backlolli (tm2, tm1) (G, SS) =
        lolli (tm1, tm2) (G, SS)

  (* Additive product types *)
  fun witH (tm1, tm2) (G, SS) =
      let
	val ((V1, L1), oc1) = tm1 (G, nilSS)
	val _ = checkType (L1, Paths.toRegion oc1)
	val ((V2, L2), oc2) = tm2 (G, nilSS)
	val _ = checkType (L2, Paths.toRegion oc2)   (* L1 = L2 = type *)
	val r = joinRegions (oc1, oc2)
      in
	case SS L2  (* ? -ic *)
	  of ((IntSyn.Nil, _), _) =>
	      ((IntSyn.With (V1, V2), L2), Paths.pair (r, oc1, oc2))
	   (* can the next case arise? *)
	   | ((S, V'), _) =>
	      error (r, "Product type applied to argument")
      end

  (* Additive unit types *)
  fun top (r) (G, SS) =
      let
	val ((S, V), os) = SS (IntSyn.Uni (IntSyn.Type))
      in
	case S
	  of IntSyn.Nil => ((IntSyn.Top, V), Paths.leaf r)
	   (* can the next case arise? *)
	   | _ => error (r, "Unit type applied to argument")
      end

  (* Explicit Type Ascription *)
  fun hastype (tm1, tm2) (G, SS) =
      let
	val ((U1, V1), oc1) = tm1 (G, nilSS)
	val ((V2, L2), oc2) = tm2 (G, nilSS)
	val _ = checkUni (L2, Paths.toRegion oc2)
	val _ = Unify.unify ((V1, IntSyn.id), (V2, IntSyn.id))
	        handle Unify.Unify(msg) =>
		  hasTypeError (G, (V1, oc1), (V2, oc2), msg)
	(* is it correct to ignore V2 and oc2 in the regions below? *)
      in
	case SS V2
	  of ((IntSyn.Nil, _), _) => ((U1, V2), oc1)
	   | ((S, V'), os) =>
	      ((IntSyn.Redex (U1, S), V'),
	       Paths.root (Paths.toRegionSpine (os, Paths.toRegion oc1), oc1, 0, os))
      end

  (* Omitted Objects (from underscore) *)
  fun omitobj (r) (G, SS) =
      let
	val V = IntSyn.newTypeVar ()
	val X = IntSyn.newEVar (V)
      in
	  case SS V
	    of ((IntSyn.Nil, V'), _) => ((X, V), Paths.leaf r) (* V = V' *)
	     | ((S, V'), _) => ((IntSyn.Redex (X, S), V'), Paths.leaf r)
      end

  (* Omitted Types (from definitions) *)
  fun omittyp (r) (G, SS) =
      let
	val X = IntSyn.newTypeVar ()
      in
	case SS (IntSyn.Uni (IntSyn.Type))
	  of ((IntSyn.Nil, L), _) => ((X, L), Paths.leaf r) (* L = type *)
	   | (S, V') => error (r, "omitted type applied to argument")
      end

  (* Dependent Function Type *)
  fun pi (decl, tm, r1) (G, SS) =
      let
	val (D1 as IntSyn.Dec (x, V1), oc1Opt) = decl G
	val ((V2, L2), oc2) = tm (IntSyn.Decl (G, D1), nilSS)
	val _ = checkUni (L2, Paths.toRegion oc2)
	val r = Paths.join (r1, Paths.toRegion oc2)
      in
	case SS L2
	  of ((IntSyn.Nil, L2'), _) =>
	       ((IntSyn.Pi ((D1, IntSyn.Maybe), V2), L2), (* L2 = L2' *)
	        Paths.bind (r, oc1Opt, oc2))
	   (* can the next case arise? *)
	   | (S, V') => error (r, "dependent function type applied to argument")
      end

  fun lam (decl, tm, r1) (G, SS) =
      case decl G
	of D1o as (IntSyn.Dec _,_) => lam1 (D1o, tm, r1) (G, SS)
         | D1o as (IntSyn.LDec _,_) => llam (D1o, tm, r1) (G, SS)

  (* Lambda Abstraction *)
  and lam1 (D1o, tm, r1) (G, SS) =
      let
	val (D1 as IntSyn.Dec (x, V1), oc1Opt) = D1o
	val ((U2, V2), oc2) = tm (IntSyn.Decl (G, D1), nilSS)
	val ((S, V), os) = SS (IntSyn.Pi ((D1, IntSyn.Maybe), V2))
	val r = Paths.join (r1, Paths.toRegion oc2)
      in
	case S
	  of IntSyn.Nil => ((IntSyn.Lam (D1, U2), V),
			    Paths.bind (r, oc1Opt, oc2))
	   | _ => ((IntSyn.Redex (IntSyn.Lam (D1, U2), S), V),
		   (* mismatch here *)
		   (Paths.root (Paths.toRegionSpine (os, r),
				Paths.bind (r, oc1Opt, oc2), 0, os)))
      end

  (* Linear Lambda Abstraction *)
  and llam (D1o, tm, r1) (G, SS) =
      let
	val (D1 as IntSyn.LDec (x, V1), oc1Opt) = D1o
	val ((U2, V2), oc2) = tm (IntSyn.Decl (G, D1), nilSS)
	val ((S, V), os) = SS (IntSyn.Pi ((D1, IntSyn.No), V2))
	val r = Paths.join (r1, Paths.toRegion oc2)
      in
	case S
	  of IntSyn.Nil => ((IntSyn.Lam (D1, U2), V),
			    Paths.bind (r, oc1Opt, oc2))
	   | _ => ((IntSyn.Redex (IntSyn.Lam (D1, U2), S), V),
		   (* mismatch here *)
		   (Paths.root (Paths.toRegionSpine (os, r),
				Paths.bind (r, oc1Opt, oc2), 0, os)))
      end

  (* Additive product types *)
  fun pair (tm1, tm2) (G, SS) =
      let
	val ((U1, V1), oc1) = tm1 (G, nilSS)
	val ((U2, V2), oc2) = tm2 (G, nilSS)
	val ((S, V), os) = SS (IntSyn.With (V1, V2))
	val r = joinRegions (oc1, oc2)
      in
	case S
	  of IntSyn.Nil => ((IntSyn.Pair (U1, U2), V),
			    Paths.pair (r, oc1, oc2))
	   (* can the next case arise? *)
	   | _ => ((IntSyn.Redex (IntSyn.Pair (U1, U2), S), V),
		   (* mismatch here *)
		   (Paths.pair (r, oc1, oc2)))
      end

  (* Additive unit element *)
  fun unit (r) (G, SS) =
      let
	val ((S, V), os) = SS (IntSyn.Top)
      in
	case S
	  of IntSyn.Nil => ((IntSyn.Unit, V), Paths.leaf r)
	   (* can the next case arise? *)
	   | _ => error (r, "Unit element applied to argument")
      end

  (* Type *)
  fun typ (r) (G, SS) =
      let
	val ((S, V), os) = SS (IntSyn.Uni (IntSyn.Kind))
      in
	case S
	  of IntSyn.Nil => ((IntSyn.Uni (IntSyn.Type), V), Paths.leaf r)
	   (* can the next case arise? *)
	   | _ => error (r, "`type' applied to argument")
      end

  (* Declarations *)
  fun decl (x, tm) (G) =
      let
	val ((V, L), oc) = tm (G, nilSS)
	val _ = checkType (L, Paths.toRegion (oc))
      in
	(IntSyn.Dec (x, V), SOME(oc))
      end

  (* Declarations with Implicit Type *)
  fun decl0 (x) (G) =
      let
	val V = IntSyn.newTypeVar ()
      in
	(IntSyn.Dec (x, V), NONE)
      end

  (* Linear Declarations *)
  fun ldecl (x, tm) (G) =
      let
	val ((V, L), oc) = tm (G, nilSS)
	val _ = checkType (L, Paths.toRegion (oc))
      in
	(IntSyn.LDec (x, V), SOME(oc))
      end

  (* Linear Declarations with Implicit Type *)
  fun ldecl0 (x) (G) =
      let
	val V = IntSyn.newTypeVar ()
      in
	(IntSyn.LDec (x, V), NONE)
      end

  (* Signature Entries *)
  datatype sgnentry =
      cdecl of name * term
    | cdefn of name * term * term
    | lcdecl of name * term

  (* Converting a term to an expression in a context *)
  (* Check that the expression is a valid type *)
  (* Throws away the associated occurrence tree *)
  fun termToExp (G, tm) =
      let
	val ((V, L), oc) = tm (G, nilSS)
	val _ = checkType (L, Paths.toRegion oc)
      in
	V
      end

  (* Converting a declaration to an expression in a context *)
  (* Throws away the associated occurrence tree *)
  fun declToDec (G, decl) =
      let
	val (D, ocOpt) = decl G
      in
	D
      end

  fun termToExp0 (tm) = tm (IntSyn.Null, nilSS)

  (* Only works properly when the Vars parameter structure *)
  (* is instantiated to EVars, not FVars *)
  (* For now allow only the simplest form of query: a type A *)
  fun termToQuery (tm) = 
      let
	val _ = Names.varReset()
	val ((V,L), oc) = (Timers.time Timers.recon termToExp0) tm
	val _ = checkType (L, Paths.toRegion oc)
	val Xs = Names.namedEVars ()
	val V' = Normalize.normalize (V, IntSyn.id)
	val _ = LinCheck.linCheckQuery (V', oc)
      in
	(V', Xs)
      end

  fun entryToEntry (cdecl(name, tm), r) =
      let
	val _ = Names.varReset ()
	val ((V, L), oc) = (Timers.time Timers.recon termToExp0) tm
	val level = getUni (L, Paths.toRegion oc)
        (* should be done in Unify, just check emptyness here *)
	(*
	val _ = if !Global.chatter >= 6
		  then TextIO.print (name ^ " :: " ^ Tools.stringExp (V) ^ "\n\n")
		else ()
	val _ = if !Global.chatter >= 5
		  then TextIO.print (name ^ " :: " ^ Tools.stringExp (Tools.normalizeExp (V, IntSyn.id)) ^ "\n\n")
		else ()
        *)
        val (imp, V') = (Timers.time Timers.abstract Abstract.abstractDecl) V
	val e = IntSyn.ConstDec (name, imp, V', level)
	val oce = Paths.decl (r, imp, oc)
	val _ = LinCheck.linCheckEntry (e, oce)
	val _ = if !Global.chatter >= 4
		  then TextIO.print ((Timers.time Timers.printing IPrint.entryToString) e ^ "\n")
		else if !Global.chatter >= 3
		       then TextIO.print ((Timers.time Timers.printing EPrint.entryToString) e ^ "\n")
		     else ()
	val _ = if !doubleCheck
		  then (Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni (level)) 
		else ()
      in
	(e, SOME(oce))
      end

    | entryToEntry (cdefn(name, tm1, tm2), r) =
      let
	val _ = Names.varReset ()
	val ((V, L), oc2) = (Timers.time Timers.recon termToExp0) tm2
	val level = getUni (L, Paths.toRegion oc2)
	val ((U, V'), oc1) = (Timers.time Timers.recon termToExp0) tm1
	val _ = (Timers.time Timers.recon Unify.unify) ((V', IntSyn.id), (V, IntSyn.id))
	        handle Unify.Unify (msg) => hasTypeError (IntSyn.Null, (V', oc1), (V, oc2), msg)
        (* should be done in Unify, just check emptyness here *)
	val (imp, (U'', V'')) = (Timers.time Timers.abstract Abstract.abstractDefn) (U, V)
	val e = IntSyn.ConstDef (name, imp, U'', V'', level)
	val oce = Paths.defn (r, imp, oc1, SOME(oc2))
	val _ = LinCheck.linCheckEntry (e, oce)
	val _ = Strictness.check (U'', V'')
        val _ = if !Global.chatter >= 4
		  then TextIO.print ((Timers.time Timers.printing IPrint.entryToString) e ^ "\n")
		else if !Global.chatter >= 3
		       then TextIO.print ((Timers.time Timers.printing EPrint.entryToString) e ^ "\n")
		     else ()
	val _ = if !doubleCheck
		  then ((Timers.time Timers.checking TypeCheck.check) (V'', IntSyn.Uni (level));
			(Timers.time Timers.checking TypeCheck.check) (U'', V''))
		else ()
      in
	(e, SOME(oce))
      end

    | entryToEntry (lcdecl(name, tm), r) =
      let
	val _ = Names.varReset ()
	val ((V, L), oc) = (Timers.time Timers.recon termToExp0) tm
	val level = getUni (L, Paths.toRegion oc)
        (* should be done in Unify, just check emptyness here *)
	(*
	val _ = if !Global.chatter >= 6
		  then TextIO.print (name ^ " :: " ^ Tools.stringExp (V) ^ "\n\n")
		else ()
	val _ = if !Global.chatter >= 5
		  then TextIO.print (name ^ " :: " ^ Tools.stringExp (Tools.normalizeExp (V, IntSyn.id)) ^ "\n\n")
		else ()
        *)
        val (imp, V') = (Timers.time Timers.abstract Abstract.abstractDecl) V
	val e = IntSyn.LinDec (name, imp, V', level)
	val oce = Paths.decl (r, imp, oc)
	val _ = LinCheck.linCheckEntry (e, oce)
	val _ = if !Global.chatter >= 4
		  then TextIO.print ((Timers.time Timers.printing IPrint.entryToString) e ^ "\n")
		else if !Global.chatter >= 3
		       then TextIO.print ((Timers.time Timers.printing EPrint.entryToString) e ^ "\n")
		     else ()
	val _ = if !doubleCheck
		  then (Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni (level)) 
		else ()
      in
	(e, SOME(oce))
      end




end; (* functor TpRecon *)
