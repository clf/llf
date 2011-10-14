(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor Modes (structure IntSyn' : INTSYN
	       structure Table : TABLE where type key = int
	       structure Names : NAMES
	       structure Paths' : PATHS)
  : MODES
  (* :> MODES
        where IntSyn = IntSyn' 
        where Paths = Paths' 
  *) =
struct
  structure IntSyn = IntSyn'
  structure Paths = Paths'
  exception Error of string

  datatype Mode = PlusPlus | Plus | Star | Minus |  MinusMinus  
  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * IntSyn.name option
   
  local 
    structure I = IntSyn'
    structure P = Paths
      
    datatype Info = Bot | Question | Top 
    datatype Status = Existential of Info * I.name option
                        | Universal
    datatype Arg = Implicit | Explicit
    (* datatype Stx = Snull | Sdecl of Stx * Status *)
    (* datatype Mtx = Mnull | Mdecl of Mtx * Marg * Arg *)

    exception Error' of P.occ * string
    fun error' (occ, msg) = raise Error' (occ, msg)
    fun error (r, msg) =
      raise Error (P.toString r ^ " " ^ "Error: " ^ (msg))

    val modeSignature : ModeSpine Table.Table = Table.new(0);

(*    ++ + * - --  mode of type where parameter occurs in

  ++  Y  Y Y Y Y
  +   Y  Y Y Y Y
  *   N  N N Y Y
  -   N  N N Y Y
  --  N  N N Y Y

  mode of parameter
*)

    fun checkName Mnil = ()
      | checkName (Mapp (Marg (_, NONE), mS)) = checkName mS  
      | checkName (Mapp (Marg (_, SOME name), mS)) = 
          let 
	    fun checkName' Mnil = ()
	      | checkName' (Mapp (Marg (_, NONE), mS)) = checkName' mS
	      | checkName' (Mapp (Marg (_, SOME name'), mS)) = 
	          if name = name'
		    then raise Error ("Variable name clash: " ^ name ^
				      " is not unique")
		  else checkName' mS
	  in
	    checkName' mS
	  end


    fun modeConsistency (PlusPlus, _) = true
      | modeConsistency (Plus, _) = true
      | modeConsistency (_, Minus) = true
      | modeConsistency (_, MinusMinus) = true
      | modeConsistency _ = false

    fun modeEqual (PlusPlus, PlusPlus) = true
      | modeEqual (Plus, Plus) = true
      | modeEqual (Star, Star) = true
      | modeEqual (Minus, Minus) = true
      | modeEqual (MinusMinus, MinusMinus) = true
      | modeEqual _ = false

    fun inferExp (mtx, mode, I.Root (I.BVar (k), S)) =
          inferSpine (inferVar (mtx, mode, k), mode, S)
      | inferExp (mtx, mode, I.Root (I.Const (cid), S)) =
	  inferSpine (mtx, mode, S)
      | inferExp (mtx, mode, I.Root (I.Defn (cid), S)) =
	  inferSpine (mtx, mode, S)
      | inferExp (mtx, mode, I.Lam (D as I.Dec (nameOpt, _), U)) =
	  I.ctxPop (inferExp (I.Decl (inferDec (mtx, mode, D),
				      (Marg (mode, nameOpt), Explicit)),
			      mode, U))
      | inferExp (mtx, mode, I.Pi ((D as I.Dec (nameOpt, _), _), V)) =
	  I.ctxPop (inferExp (I.Decl (inferDec (mtx, mode, D),
				      (Marg (mode, nameOpt), Explicit)),
			      mode, V))

    and inferSpine (mtx, mode, I.Nil) = mtx
      | inferSpine (mtx, mode, I.App (U, S)) = 
          inferSpine (inferExp (mtx, mode, U), mode, S)
	  
    (*     + * -
        --------
	+  + + +
        *  + * -
	-  + - -   *)
        
    and inferVar (I.Decl (mtx, (Marg (Star, nameOpt), Implicit)), mode, 1) = 
          I.Decl (mtx, (Marg (mode, nameOpt), Implicit))
      | inferVar (I.Decl (mtx, (Marg (_, nameOpt), Implicit)), Plus, 1) = 
          I.Decl (mtx, (Marg (Plus, nameOpt), Implicit))
      | inferVar (mtx as I.Decl (_, (_, Implicit)), _, 1) = 
	  mtx
      | inferVar (mtx as I.Decl (_, (Marg (mode', SOME name), Explicit)),
		  mode, 1) =  
	  if modeConsistency (mode', mode) then mtx 
	  else raise  Error ("mode declaration for " ^ name ^
			     " expected to be + or ++")
      | inferVar (I.Decl (mtx, (marg as Marg (mode', _), arg)), mode, k) = 
	  I.Decl (inferVar (mtx, mode, (k -1)), (marg, arg))
	  
    and inferDec (mtx, mode, I.Dec (_, V)) = 
          inferExp (mtx, mode, V)
      
    fun inferMode ((mtx, I.Uni(I.Type)), Mnil) = mtx
      | inferMode ((_, I.Uni(I.Type)), _) =
          raise Error "Too many modes specified"
      | inferMode ((mtx, I.Pi ((I.Dec (name, V1), _), V2)),
		   Mapp (Marg (mode, _), mS)) =
          I.ctxPop (inferMode ((I.Decl (inferExp (mtx, mode, V1),
					(Marg (mode, name), Explicit)), V2),
			       mS))
      | inferMode ((mtx, I.Root _), _) =
	  raise Error "type constant expected, object constant found" 
      | inferMode _ = raise Error "Not enough modes specified"

    fun abstractMode (mtx, mS) =
      let
	fun abstractMode' (I.Null, mS, _) = mS
	  | abstractMode' (I.Decl (mtx, (marg, _)), mS, k) = 
              abstractMode' (mtx, Mapp (marg, mS), k+1)
      in
	abstractMode' (mtx, mS, 1)
      end
    (* make sure the the parameter names are different from all other variables
       in mtx --cs *)

    (* modeLookup (cid) = mS
     
       Invariant:
       cid has a mode!
       ModeSpine mS for the constant cid is looked up an 
       returned. If |mode signature| < cid, return Mnil 
    *)

    fun modeLookup' (cid, occ) =  
      case (Table.lookup modeSignature cid) of NONE => 
	  raise error' (occ, "Identifier " ^ (I.entryName (I.sgnLookup cid)) ^
			" expected to be moded")
      | SOME sM => sM 

    fun modeLookup cid = modeLookup' (cid, P.top)



    fun checkConsExp (mtx, I.Root (I.BVar (k), S), mode) =
          (checkConsVar(mtx, k, mode); 
	  checkConsSpine(mtx, S, mode))
      | checkConsExp (mtx, I.Root (I.Const (c), S), mode) =
	  checkConsSpine (mtx, S, mode)
      | checkConsExp (mtx, I.Root (I.Defn (d), S), mode) =
	  checkConsSpine (mtx, S, mode)
      | checkConsExp (mtx, I.Lam (D as I.Dec (nameOpt, _), U), mode) =
	  (checkConsDec (mtx, D, mode);
	   checkConsExp (I.Decl (mtx, (Marg (mode, nameOpt), Explicit)), U,
			 mode)) 
      | checkConsExp (mtx, I.Pi ((D as I.Dec (nameOpt, _), _), V), mode) =
	  (checkConsDec (mtx, D, mode);
	   checkConsExp (I.Decl (mtx, (Marg (mode, nameOpt), Explicit)), V,
			 mode)) 

    and checkConsSpine (mtx, I.Nil, mode) = ()
      | checkConsSpine (mtx, I.App (U, S), m) =
          (checkConsExp (mtx, U, m); checkConsSpine (mtx, S, m))
	  
    and checkConsVar (I.Decl (mtx, (Marg (mode', nameOpt), _)), 1, mode) = 
          if modeEqual (mode', mode) then () 
	  else (case nameOpt of 
		  NONE => raise Error "mode for implicit variable in defined type is inconsistent"
		| SOME name => raise Error ("mode for " ^ name ^
					    " in defined type is inconsistent"))
      | checkConsVar (I.Decl (mtx, _), k, mode) =
	  checkConsVar (mtx, k-1, mode)
	    
    and checkConsDec (mtx, I.Dec (_, V), mode) = checkConsExp (mtx, V, mode)
	    
    fun  checkDefnSpine (mtx, I.Nil, Mnil) = ()
      | checkDefnSpine (mtx, I.App (U, S), Mapp (Marg(m, _), mS)) =
          (checkConsExp (mtx, U, m); checkDefnSpine (mtx, S, mS))

    fun checkDefn (mtx, I.Lam (D, V), Mapp (marg, mS)) =
          checkDefn (I.Decl  (mtx, (marg, Explicit)), V, mS)
      | checkDefn (mtx, I.Root (I.Const (c) , S), Mnil) = 
	  checkDefnSpine (mtx, S, modeLookup (c))
          (* no other cases by invariant *)
	  

    fun empty (0, ctx, V) = (ctx, V)
      | empty (k, ctx, I.Pi (_, V)) =
          empty (k-1, I.Decl (ctx, (Marg (Star, NONE), Implicit)), V)
 
	
    (* modeReset () = ()

       Invariant: 
       After modeReset is invoked, the size of the 
       mode array is reset to 0
       (side effect!)
    *)
    fun modeReset () = Table.clear modeSignature

    fun calcImplicit (cid, mS, r) =
      let 
	fun calcImplicit' (I.ConstDec (_, k, V, _))  =
	      abstractMode (inferMode (empty (k, I.Null, V), mS), mS)
	  | calcImplicit' (I.ConstDef (_, k, U, V, _)) =
	      let val mS' = abstractMode (inferMode (empty (k, I.Null, V), mS), mS)
	      in 
		(checkDefn (I.Null, U, mS'); mS')
	      end
      in 
	(checkName mS; calcImplicit' (I.sgnLookup cid))
	handle Error s => error (r, s)
     end

    fun checkConsistency (cid, mS, r) =  
      (checkName mS; 
       case I.sgnLookup cid of
	 I.ConstDec (_, _, V, _)  =>
	   (inferMode ((I.Null, V), mS); ())
       | I.ConstDef (_, _, U, V, _) =>
	   (inferMode ((I.Null, V), mS);
	    checkDefn (I.Null, U, mS)))
         handle Error s =>  error (r, s)
		  
    (* modeAdd (cid, mS) = ()
        
       Invariant:
       The ModeSpine mS  is stored with the type constant cid
       (side effect!)
    *)

    fun modeAdd (cid, mS) = 
      Table.insert modeSignature (cid, mS) 


    fun installMode (cid, mS) =
          modeAdd (cid, mS)
	    (* this check is unnecessary here, by invariant (identifier
	     validity is already checked during mode reconstruction) --cs *)


    (* unique (k, S) = B

       Invariant:
       B iff k does not occur in S
    *)

    fun unique (k, I.Nil) = true
      | unique (k, (I.App (I.Root (I.BVar (k'), I.Nil), S))) =
          (k <> k') andalso unique (k, S)


    (* isPattern (St, k, mS) = B
     
       Invariant: 
       B iff k > k' for all k' in mS
	 and for all k in mS: k is parameter
         and for all k', k'' in mS: k' <> k''
    *)

    fun isUniversal Universal = true
      | isUniversal _ = false

    fun isTop (Existential (Top, _)) = true
      | isTop _ = false

    fun isQuestion (Existential (Question, _)) = true
      | isQuestion _ = false

    fun isBot (Existential (Bot, _)) = true
      | isBot _ = false

    fun nameOf (Existential (_, NONE)) = "?"
      | nameOf (Existential (_, SOME name)) = name
      | nameOf _ = "?"
      
    fun isPattern (St, k, I.Nil) = true
      | isPattern (St, k, I.App (I.Root (I.BVar (k'), I.Nil), S)) =
          (k > k') 
	  andalso isUniversal (I.ctxLookup (St, k'))
	  (* changed order of checks below so unique is complete -fp *)
	  andalso isPattern (St, k, S)
	  andalso unique (k', S) 
      | isPattern _ = false

    (* updateExpD (St, U, mode) = St'
     
       If   G |- U : V 
       and  St ~ G
       then St' = St where all EVars in U change their status:
	 
	       | +    -
	 ----------------
	 par   | par  par
	 top   | top  top
	 ?     | top  ?
	 bot   | top  ?
    *)

    fun updateExpD (St, I.Root (I.BVar (k), S), mode) =
          if isUniversal (I.ctxLookup (St, k)) 
	    then updateSpineD (St, S, mode)
	  else 
	    if isPattern (St, k, S) then updateVarD (St, k, mode)
	    else 
	      if mode = Minus then updateSpineD (St, S, mode)
	      else St
      | updateExpD (St, I.Root (I.Const (c), S), mode) =
	  updateSpineD (St, S, mode)
      | updateExpD (St, I.Root (I.Defn (d), S), mode) =
	  updateSpineD (St, S, mode)
      | updateExpD (St, I.Lam (D, U), mode) =
	  I.ctxPop (updateExpD (I.Decl (St, Universal), U, mode))


    and updateSpineD (St, I.Nil, mode) = St
      | updateSpineD (St, I.App (U, S), mode) = 
          updateSpineD (updateExpD (St, U, mode), S, mode)

    (* Invariant: k is not a parameter *)
 
    and updateVarD (I.Decl (St, Existential (i, name)), 1, Plus) =
         I.Decl (St, Existential (Top, name))
      | updateVarD (I.Decl (St, S as Existential (Top, _)), 1, mode) =
	 I.Decl (St, S)    
          (* mode = Minus | MinusMinus    by invariant *)
      | updateVarD (I.Decl (St, S as Existential (Question, _)), 1, mode) =
	 I.Decl (St, S)
          (* mode = Minus | MinusMinus    by invariant *)
      | updateVarD (I.Decl (St, Existential (Bot, name)), 1, mode) =
	 I.Decl (St, Existential (Question, name))
          (* mode = Minus | MinusMinus    by invariant *)
      | updateVarD (I.Decl (St, s), k, mode) = 
          I.Decl(updateVarD (St, (k - 1), mode), s)

    (* updateExpD (St, S, mS) = St'
     
       If   G |- S : V > V' 
       and  St ~ G 
       and  S ~ mS
       then St' = St where 
            all EVars in S(i) change their status according mS(i) in the
	    table above.
    *)

    fun propagateD (St, I.Nil, Mnil) = St
      | propagateD (St, I.App (U, S), Mapp (Marg (Star, _), mS)) =
          propagateD (St, S, mS) 
      | propagateD (St, I.App (U, S), Mapp (Marg (PlusPlus, _), mS)) =
	  propagateD (St, S, mS)
      | propagateD (St, I.App (U, S), Mapp (Marg (mode, _), mS)) =
          propagateD (updateExpD (St, U, mode), S, mS) 

    fun propagatePlusPlusD (St, I.Nil, Mnil, _) = St
      | propagatePlusPlusD (St, I.App (I.Root (I.BVar k, S'), S),
			    Mapp (Marg (PlusPlus, _), mS), (p, occ)) =
          let 
	    val status = (I.ctxLookup (St, k))
	  in
	    if isBot status andalso isPattern (St, k, S')
	      then propagatePlusPlusD (updateVarD (St, k, Plus), S, mS,
				       (p+1, occ))
	    else error' (P.arg (p, occ), "++ argument " ^ (nameOf status) ^
			 " is already ground")
	  end
      | propagatePlusPlusD (St, _, Mapp (Marg (PlusPlus, _), mS), (p, occ)) =
	  error' (P.arg (p, occ), "++ argument not a variable") 
            (* print part of the term? *)
      | propagatePlusPlusD (St, I.App (U, S), Mapp (_, mS), (p, occ)) =
	  propagatePlusPlusD (St, S, mS, (p+1, occ))

    (* checkExpPlus (St, U)  = () 

       If   G |- U : V
       and  St ~ G
       then function succeeds 
	    if all EVar's in U are assumed to be ground with respect to St
    *)

    fun checkExpPlus (St, I.Root (I.BVar k, S), occ) =
          (checkVarPlus (St, k, P.head occ); checkSpinePlus (St, S, (1, occ)))
      | checkExpPlus (St, I.Root (I.Const c, S), occ) =
	  checkSpinePlus (St, S, (1, occ))
      | checkExpPlus (St, I.Root (I.Defn d, S), occ) =
	  checkSpinePlus (St, S, (1, occ))
      | checkExpPlus (St, I.Lam (D, U), occ) =
	  checkExpPlus (I.Decl (St, Universal), U, P.body occ)

    and checkSpinePlus (St, I.Nil, _) = ()
      | checkSpinePlus (St, I.App (U, S), (p, occ)) =
          (checkExpPlus (St, U, P.arg (p, occ));
	   checkSpinePlus(St, S, (p+1, occ)))

    and checkVarPlus (St, k, occ) =
          let
	    val status = I.ctxLookup (St, k) 
	  in 
	    if isTop status orelse isUniversal status then ()
	    else error' (occ, "+ argument " ^ (nameOf status) ^
			 " in recursive call not necessarily ground")
	  end

    (* checkPlus (St, S, mS)  = () 

       If   G |- S : V > V' 
       and  St ~ G 
       and  S ~ mS
       then function succeeds 
	    if all S(i) in are assumed to be ground if mS(i) = +
    *)

    fun checkPlus (St, I.Nil, Mnil, _) = ()
      | checkPlus (St, I.App (U, S), Mapp (Marg (Plus, _), mS), (p, occ)) =
          (checkExpPlus (St, U, P.arg (p, occ));
	   checkPlus (St, S, mS, (p+1, occ)))
      | checkPlus (St, I.App (U, S), Mapp (Marg (PlusPlus, _), mS), (p, occ)) =
          (checkExpPlus (St, U, P.arg (p, occ));
	   checkPlus (St, S, mS, (p+1, occ)))
      | checkPlus (St, I.App (U, S), Mapp (Marg (mode, _), mS), (p, occ)) =
          checkPlus (St, S, mS, (p, occ))
	     (* mode = Minus | MinusMinus | Star *)


    (* assumeExpMinus (St, U)  = St' 

       If   G |- U : V
       and  St ~ G
       then all EVar's in U, moded with - are assumed to be ground (top)
            in St'.
    *)

    fun assumeExpMinus (St, I.Root (I.BVar (k), S)) =
          if isUniversal (I.ctxLookup (St, k))
	    then assumeSpineMinus (St, S)
	  else 
	    if isPattern (St, k, S) then assumeVarMinus (St, k)
	    else St
      | assumeExpMinus (St, I.Root (I.Const (c), S)) =
	  assumeSpineMinus (St, S)
      | assumeExpMinus (St, I.Root (I.Defn (d), S)) =
	  assumeSpineMinus (St, S)
      | assumeExpMinus (St, I.Lam (D, U))= 
	  I.ctxPop (assumeExpMinus (I.Decl (St, Universal), U))
	  

    and assumeSpineMinus (St, I.Nil) = St
      | assumeSpineMinus (St, I.App (U, S)) = 
          assumeSpineMinus (assumeExpMinus (St, U), S)
	  
    and assumeVarMinus (I.Decl (St, Existential (i, name)), 1) =
          I.Decl (St, Existential (Top, name))
      | assumeVarMinus (I.Decl (St, s), k) = 
          I.Decl (assumeVarMinus (St, (k-1)), s)


    (* assumeExpMinus (St, S, mS)  = St' 
 
       If   G |- S : V > V' 
       and  St ~ G 
       and  S ~ mS
       then For all i, if mS(i)= i then all Evar's moded with -
            in S(i) are assumed ground (top) in St'
    *)
    fun assumeMinus (St, I.Nil, Mnil) = St
      | assumeMinus (St, I.App (U, S), Mapp (Marg (Minus, _), mS)) = 

	  assumeMinus (assumeExpMinus (St, U), S, mS)
      | assumeMinus (St, I.App (U, S), Mapp (Marg (mode, _), mS)) = 
	  (* mode = MinusMinus | Star | Plus | PlusPlus   by invariant *)
	  assumeMinus (St, S, mS)

    fun assumeMinusMinus (St, I.Nil, Mnil, _) = St
      | assumeMinusMinus (St, I.App (I.Root (I.BVar k, S'), S),
			  Mapp (Marg (MinusMinus, _), mS), (p, occ)) =
          let 
	    val status = (I.ctxLookup (St, k))
	  in
	    if Bool.not (isTop status) andalso isPattern (St, k, S')
	      then assumeMinusMinus (assumeVarMinus (St, k), S, mS, (p+1, occ))
	    else error' (P.arg (p, occ), "-- argument " ^ (nameOf status)  ^
			 " is already ground")
	  end
      | assumeMinusMinus (St, _, Mapp (Marg (MinusMinus, _), mS), (p, occ)) =
	  error' (P.arg (p, occ), "-- argument not a variable")
      | assumeMinusMinus (St, I.App (U, S), Mapp (Marg (mode, _), mS),
			  (p, occ)) =
	    (* mode = Minus | Star | Plus | PlusPlus   by invariant *)
	  assumeMinusMinus (St, S, mS, (p+1, occ))
	    
    (* modeCheckD (St, V)  = St' 

       If   G |- V : L
       and  St ~ G
       then St' is the result of modechecking V 
    *)
    fun modeCheckD (St, I.Pi ((I.Dec (name,_), I.Maybe), D), occ) = 
          let 
	    val I.Decl (St', status) = modeCheckD (I.Decl (St, Existential (Bot, name)), D, P.body occ)
	  in 
	    if isQuestion status
	      then error' (P.body occ, "- argument " ^ nameOf status ^
			   " is not well-moded ")
	    else St' 
	  end
      | modeCheckD (St, I.Pi ((G as I.Dec (name, _), I.No), D), occ) = 
          let 
	    val I.Decl (St', status) = modeCheckD (I.Decl (St, Existential (Bot, name)), D, P.body occ) (* status = bot by invariant *)
	  in
	    modeCheckDecG (St', G, P.label occ)
	  end 
      | modeCheckD (St, I.Root (I.Const c, S), occ) =
	  let 
	    val mS = modeLookup' (c, occ) 
	  in 
	    propagateD (propagatePlusPlusD (St, S, mS, (1, occ)), S, mS)
	  end
      | modeCheckD (St, I.Root (I.Defn c, S), occ) =
	  let 
	    val mS = modeLookup' (c, occ) 
	  in 
	    propagateD (propagatePlusPlusD (St, S, mS, (1, occ)), S, mS)
	  end
	
    and modeCheckDecD (St, I.Dec (_, V), occ) = modeCheckD (St, V, occ) 


    (* modeCheckG (St, V)  = St' 

       If   G |- V : L
       and  St ~ G
       then St' is the result of modechecking V 
    *)
    and modeCheckG (St, I.Pi ((_, I.Maybe), G), occ) = 
          I.ctxPop (modeCheckG (I.Decl (St, Universal), G, P.body occ))
            (* I.ctxPop, possible, because top element is a parameter *)
      | modeCheckG (St, I.Pi ((D, I.No), G), occ) = 
          let 
	    val _ = modeCheckDecD (St, D, P.label occ)
	  in
	    I.ctxPop (modeCheckG (I.Decl (St, Universal), G, P.body occ))
	      (* I.ctxPop, possible, because top element is a parameter *)
	  end 
      | modeCheckG (St, I.Root (I.Const c, S), occ) =
	  let 
	    val mS = modeLookup' (c, occ)
	  in 
	    (checkPlus (St, S, mS, (1, occ));
	     assumeMinus (assumeMinusMinus(St, S, mS, (1, occ)), S, mS))
	  end
      | modeCheckG (St, I.Root (I.Defn d, S), occ) =
	  let 
	    val mS = modeLookup' (d, occ)
	  in 
	    (checkPlus (St, S, mS, (1, occ));
	     assumeMinus (assumeMinusMinus(St, S, mS, (1, occ)), S, mS))
	  end

    and modeCheckDecG (St, I.Dec (_, V), occ) = modeCheckG (St, V, occ) 


    fun checkD (cid, ocOpt) = 
      let 
	fun checkable (I.Root (I.Const (c), _)) = 
	      (case (Table.lookup modeSignature c) of NONE => false
		| SOME _ => true)
	  | checkable (I.Uni _) = false
	  | checkable (I.Pi (_, V)) = checkable V
	  | checkable (I.Top) = false
	  | checkable (I.With (V1, V2)) = false        (* for the moment -ic *)
	val V = I.constType cid
      in
        if (checkable V)
	  then (modeCheckD (I.Null, V, P.top); ())
	    handle Error' (occ, msg) =>   
	      (case ocOpt of  
		 NONE => raise Error msg
	       | SOME occTree => error (P.occToRegionDecl occTree occ, msg))
	else ()
      end

    fun checkG (V, ocOpt) = (modeCheckG (I.Null, V, P.top); ())
      handle Error' (occ, msg) =>   
	(case ocOpt of 
	   NONE => raise Error msg
	 | SOME occTree => error (P.occToRegionDecl occTree occ, msg))


  in
    val reset = modeReset
    val calcImplicit = calcImplicit
    val checkConsistency = checkConsistency
    val installMode = installMode
    val lookup = modeLookup
    val checkD = checkD
    val checkG = checkG
  end
end;  (* functor Modes *)
