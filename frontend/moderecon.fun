(* Reconstructing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor ModeRecon (structure Global : GLOBAL
		   structure IntSyn: INTSYN
		   structure Pattern : PATTERN
		     sharing Pattern.IntSyn = IntSyn
		   structure Modes' : MODES
		     sharing Modes'.IntSyn = IntSyn
		   structure Paths' : PATHS
		     sharing Modes'.Paths = Paths'
		   structure EModePrint : MODEPRINT
		     sharing EModePrint.Modes = Modes'
		   structure IModePrint : MODEPRINT
		     sharing IModePrint.Modes = Modes'
		   structure Unify : UNIFY
		     sharing Unify.IntSyn = IntSyn
		   structure TpRecon' : TP_RECON
		     sharing TpRecon'.IntSyn = IntSyn)
  : MODE_RECON
  (* :> MODE_RECON
        where ExtSyn = TpRecon'
        where Modes = Modes' 
        where Paths = Paths'
  *) =
struct
  structure Modes = Modes'
  structure ExtSyn = TpRecon'
  structure Paths = Paths'
    
  type mode = Modes.Mode * Paths.region

  (* datatype Mtx = Mnull | Mdecl of Mtx * Modes.Mode    (* it would be nice if we could move this *)
  *)

  fun plusplus r = (Modes.PlusPlus, r)
  fun plus r = (Modes.Plus, r)
  fun star r = (Modes.Star, r)
  fun minus r = (Modes.Minus, r)
  fun minusminus r = (Modes.MinusMinus, r)
  (* region information currently omitted: can be extended to 
     occurence trees *)

  type termIm =  IntSyn.cid * Modes.ModeSpine
  type spineIm = Modes.ModeSpine * Paths.region
    
  type termEx = IntSyn.dctx * Modes.Mode IntSyn.Ctx
                -> IntSyn.cid * Modes.ModeSpine

  type termM = IntSyn.cid * Modes.ModeSpine
    
  exception Error of string

  local
    structure I = IntSyn
    structure M = Modes
    structure T = ExtSyn
    structure P = Paths

    fun error (r, msg) =
      raise Error (P.toString r ^ " " ^ "Error: " ^ (msg))

    fun nilIm r = (M.Mnil, r)
    fun appIm (((m, r1), n), (s, r2)) = (M.Mapp (M.Marg (m, n), s), Paths.join (r1, r2))
    fun rootIm (n, r1, (s, r2)) = 
      let val r = P.join (r1, r2)
      in
	(case Names.nameLookup n of 
	   NONE => error (r, "Undeclared identifier " ^ n ^ " cannot be moded")
	 | SOME cid => (cid, M.calcImplicit (cid, s, r)))
      end
    fun implicit nmS = nmS

    fun piEx ((m, _), d, t) (G, D) =  
      t (I.Decl (G, T.declToDec (G, d)), I.Decl (D, m))


    fun convertSpine (_, I.Nil) = M.Mnil
      | convertSpine (GD as (G, D), I.App (U, S)) = 
          let 
	    val k = Pattern.etaContract U
	    val I.Dec (name, V) = I.ctxDec (G, k) 
	    val mode = I.ctxLookup (D, k)
	  in
	    M.Mapp (M.Marg (mode, name), convertSpine (GD, S))
	  end

    fun convertExp (GD, I.Root (I.Const (c), S))  = 
          (c, convertSpine (GD, S))
      | convertExp (GD, I.Root (I.Defn (d), S))  = 
          (d, convertSpine (GD, S))

    fun rootEx (t, r) (GD as (G, D)) = 
      let
	val (c, mS) = convertExp (GD, T.termToExp (G, t))
      in (M.checkConsistency (c, mS, r);  (c, mS))
      end

    fun explicit t = 
      let 
(*	val _ = Unify.Constraints.reset () *)
	val nmS = t (I.Null, I.Null)
(*	val _ = Unify.resolveConstraints () *)
      in
	nmS
      end

    fun modeToMode m =
      let
	val _ = 
	  if !Global.chatter >= 4
	    then TextIO.print ("%mode " ^ (IModePrint.modeToString m) ^ ".\n")
	  else if !Global.chatter >= 3 
		 then TextIO.print ("%mode " ^ (EModePrint.modeToString m) ^ ".\n")
	       else ()
      in m
      end
  in
    val modeToMode = modeToMode
    val nilIm = nilIm
    val appIm = appIm
    val rootIm = rootIm
    val piEx = piEx
    val rootEx = rootEx
    val explicit = explicit
    val implicit = implicit
  end (* local *)
end (* functor ModeRecon *)
    


