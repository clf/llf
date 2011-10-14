(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

functor FrontEnd
  (structure Global : GLOBAL
   structure IntSyn' : INTSYN
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Modes : MODES
   structure Lexer : LEXER		(* for errors only *)
   structure Parsing : PARSING
     sharing Parsing.Lexer = Lexer	(* necessary? *)
   structure Parser : PARSER
     sharing Parser.Names = Names
   structure TypeCheck : TYPECHECK	(* for errors only *)
   structure Strictness : STRICTNESS	(* for errors only *)
   structure Constraints : CONSTRAINTS		
     sharing Constraints.IntSyn = IntSyn'
   structure Abstract : ABSTRACT	(* for errors only *)
   structure Origins : ORIGINS
   structure TpReconQ : TP_RECON
     sharing TpReconQ.IntSyn = IntSyn'
     sharing TpReconQ.Paths = Modes.Paths
     sharing type TpReconQ.term = Parser.ExtSynQ.term
     sharing type TpReconQ.Paths.occEntry = Origins.Paths.occEntry
   structure TpRecon : TP_RECON
     sharing TpRecon.IntSyn = IntSyn'
     sharing TpRecon.Paths = Modes.Paths
     sharing type TpRecon.sgnentry = Parser.ExtSyn.sgnentry
     sharing type TpRecon.term = Parser.ExtSyn.term
     sharing type TpRecon.Paths.occEntry = Origins.Paths.occEntry
   structure ModeRecon : MODE_RECON
     sharing ModeRecon.Modes = Modes
     sharing type ModeRecon.termM = Parser.ExtModes.termM
   structure Lex : LEX
   structure LexRecon : LEX_RECON
     sharing LexRecon.LexSyn = Lex.LexSyn
     sharing LexRecon.Paths = Modes.Paths
     sharing type LexRecon.term = Parser.LexSynExt.term
   structure LinCheck : LINCHECK
     sharing LinCheck.IntSyn = IntSyn'
   structure Timers : TIMERS
   structure Index : INDEX
     sharing Index.IntSyn = IntSyn'
   structure CompSyn' : COMPSYN
     sharing CompSyn'.IntSyn = IntSyn'
   structure Compile : COMPILE
     sharing Compile.IntSyn = IntSyn'
     sharing Compile.CompSyn = CompSyn'
   structure Trail : TRAIL
     sharing Trail.IntSyn = IntSyn'
   structure AbsMachine : ABSMACHINE
     sharing AbsMachine.IntSyn = IntSyn'
     sharing AbsMachine.CompSyn = CompSyn'
   structure IPrint : PRINT
     sharing IPrint.IntSyn = IntSyn'
   structure EPrint : PRINT
     sharing EPrint.IntSyn = IntSyn'
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn')
 :> FRONT_END =
struct

  structure IntSyn = IntSyn'
  structure S = Parser.Stream

  fun fileOpenMsg (fileName) =
      (case !Global.chatter
	 of 0 => ()
	  | 1 => TextIO.print ("[Loading file " ^ fileName ^ " ...")
          | _ => TextIO.print ("[Opening file " ^ fileName ^ "]\n"))

  fun fileCloseMsg (fileName) =
      (case !Global.chatter
         of 0 => ()
	  | 1 => TextIO.print ("]\n")
          | _ => TextIO.print ("[Closing file " ^ fileName ^ "]\n"))

  (* val withOpenIn : string -> (TextIO.instream -> 'a) -> 'a *)
  fun withOpenIn (fileName) (scope) =
      let
	val instream = TextIO.openIn fileName
	val _ = fileOpenMsg (fileName)
	val timer = Timer.startCPUTimer ()
	val result = scope instream
		     handle exn => (TextIO.closeIn instream;
				    fileCloseMsg (fileName);
				    raise exn )
	val _ = fileCloseMsg (fileName)
	val _ = TextIO.closeIn instream
      in
	result
      end;

  fun evarInstToString (Xs) =
      (Names.varReset () ;		(* -ic 5/28/99 *)
       if !Global.chatter >= 4
	  then IPrint.evarInstToString (Xs)
	else if !Global.chatter >= 3
	       then EPrint.evarInstToString (Xs)
	     else "")

  fun linCheckAnswer nil = ()
    | linCheckAnswer ((U,N) :: Xs) =
        ((LinCheck.linCheck (U, NONE)
	  handle LinCheck.Warning msg =>
	          (if !Global.chatter >= 3
		     then TextIO.print ("Warning for " ^ N ^ ":" ^ msg ^ "\n")
	     else ())) ;
	 linCheckAnswer Xs)

  fun expToString GU =
      if !Global.chatter >= 4
	then IPrint.expToString GU
      else if !Global.chatter >= 3
	     then EPrint.expToString GU
	   else ""

  datatype Status = OK | ABORT
  fun abort (msg) = (TextIO.print (msg); ABORT)
  fun abortFileMsg (fileName, msg) = abort (fileName ^ ":" ^ msg ^ "\n")

  fun abortIO (fileName, {cause = OS.SysErr (msg, _), function = f, name = n}) =
      (TextIO.print ("IO Error on file " ^ fileName ^ ":\n" ^ msg ^ "\n");
       ABORT)
    | abortIO (fileName, {function = f, ...}) =
      (TextIO.print ("IO Error on file " ^ fileName ^ " from function "
		     ^ f ^ "\n");
       ABORT)

  fun wrapRegion (r, msg) = (Lexer.Paths.toString r ^ " " ^ "Error:\n" ^ msg)

  val compiled = ref false
  exception Uncompiled

  exception AbortQueries of string

  fun handleExceptions fileName (f:'a -> Status) (x:'a) =
      (f x
       handle TpRecon.Error (msg) => abortFileMsg (fileName, msg)
	    | TpReconQ.Error (msg) => abortFileMsg (fileName, msg)
	    | ModeRecon.Error (msg) => abortFileMsg (fileName, msg)
	    | LexRecon.Error (msg) => abortFileMsg (fileName, msg)
	    | TypeCheck.Error (msg) => abort ("Type checking error: " ^ msg ^ "\n")
	    | LinCheck.Error (msg) => abortFileMsg (fileName, msg)
	    | LinCheck.Warning (msg) => abortFileMsg ("Warning : " ^ fileName, msg)
	    | Strictness.Error (msg) => abort ("Strictness error: " ^ msg ^ "\n")
	    | Abstract.Error (msg) => abort ("Abstraction error: " ^ msg ^ "\n")
	    | Modes.Error (msg) => abortFileMsg (fileName, msg)
	    | Parsing.Error (msg) => abortFileMsg (fileName, msg)
	    | Lexer.Error (msg) => abortFileMsg (fileName, msg)
	    | IntSyn.Error (msg) => abort ("Signature error: " ^ msg ^ "\n")
	    | Names.Error (msg) => abortFileMsg (fileName, msg)
	    | IO.Io (ioError) => abortIO (fileName, ioError)
	    | AbortQueries (msg) => abort ("Queries aborted:\n" ^ msg ^ "\n")
	    | Uncompiled =>
	      abort ("Query error: Program has not been compiled!\n" ^ 
		     "Use FrontEnd.compileConfig (config) or FrontEnd.compile ().\n")
	    | exn => (abort ("Unrecognized exception\n"); raise exn))

  (* Bounds SOME(n) for n >= 0, NONE represents positive infinity *)
  (* Concrete syntax: 0, 1, 2, ..., * *)
  type bound = int option

  (* exceeds : bound * bound -> bool *)
  fun exceeds (SOME(n), SOME(m)) = (n >= m)
    | exceeds (SOME(n), NONE) = false
    | exceeds (NONE, _) = true

  (* boundEq : bound * bound -> bool *)
  fun boundEq (SOME(n), SOME(m)) = (n = m)
    | boundEq (NONE, NONE) = true
    | boundEq _ = false

  (* boundToString : bound -> string *)
  fun boundToString (SOME(n)) = Int.toString (n)
    | boundToString (NONE) = "*"

  (* boundMin : bound * bound -> bound *)
  fun boundMin (SOME(n), SOME(m)) = SOME(Int.min (n,m))
    | boundMin (b, NONE) = b
    | boundMin (NONE, b) = b

  (* checkSolutions : bound * bound * int -> unit *)
  (* raises AbortQueries(msg) if the actual solutions do not match *)
  (* the expected number, given the bound on the number of tries *)
  fun checkSolutions (expected, try, solutions) =
      if boundEq (boundMin (expected, try), SOME(solutions))
	then ()
      else raise AbortQueries ("Wrong number of solutions: expected "
			       ^ boundToString expected ^ " in "
			       ^ boundToString try ^ " tries, but found "
			       ^ Int.toString solutions)

  fun moreSolutions () =
      (TextIO.print ("More? ");
       case String.sub (TextIO.inputLine (TextIO.stdIn), 0)
	 of #"y" => true
          | #"Y" => true
	  | #";" => true
	  | #"q" => raise AbortQueries("Explicit quit")
	  | #"Q" => raise AbortQueries("Explicit Quit")
	  | _ => false)

  exception Done

  fun readFile (fileName) = 
      handleExceptions fileName (withOpenIn fileName)
       (fn instream =>
	let
	  fun install s = install' ((Timers.time Timers.parsing S.expose) s)
	  and install' (S.Empty) = OK
	    | install' (S.Cons(Parser.SgnEntry(sgnentry, r), s')) =
	      let
		val (entry, ocOpt) = TpRecon.entryToEntry (sgnentry, r)
		val cid = IntSyn.sgnAdd entry (* updates global signature *)
		val _ = Names.installName (IntSyn.entryName entry, cid)
		val _ = Origins.installOrigin (cid, ocOpt)
		val _ = (Timers.time Timers.modes Modes.checkD) (cid, ocOpt)
	      in
		install s'
	      end

            | install' (S.Cons(Parser.Query(expected,try,query), s')) =
              let
		val _ = if not(!compiled)
			  then raise Uncompiled
			else ()
		val _ = if !Global.chatter >= 2
			  then TextIO.print ("%query " ^ boundToString expected
				      ^ " " ^ boundToString try)
			else ()
                val (A, Xs) = TpReconQ.termToQuery(query)  (* times itself *)
		val _ = if !Global.chatter >= 2
			  then TextIO.print (" ")
			else ()
		val _ = if !Global.chatter >= 3
			  then TextIO.print
			        ("\n"
				 ^ (Timers.time Timers.printing expToString)
				   (IntSyn.Null, A)
				 ^ ".\n")
			else ();
		(* If we printed the query, possibly containing new variables *)
                (* we need to extend the answer substitution for thos variables *)
		(* This does not work, because new EVars may not necessarily *)
		(* be global! *)
		(*
		val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
		*)
                val g = (Timers.time Timers.compiling Compile.compileGoal) A
		val solutions = ref 0
		fun scInit M =
		  (linCheckAnswer Xs ;
		   if !Global.chatter >= 3
		     then TextIO.print ((Timers.time Timers.printing evarInstToString) Xs ^ "\n")
		   else if !Global.chatter >= 2
			  then TextIO.print "."
			else ();
		   if !Global.chatter >= 3
		     then TextIO.print ((Timers.time Timers.printing evarInstToString) [(M, "%P")] ^ "\n")
		   else ();
		   if !Global.chatter >= 3
		     then Constraints.warnConstraints (Names.evarCnstr ())
		   else ();
		   solutions := !solutions+1;
		    if exceeds (SOME(!solutions),try)
		      then raise Done
		    else ())
              in
		if not (boundEq (try, SOME(0)))
		  then (Trail.reset ();
			((Timers.time Timers.solving AbsMachine.solve)
			 ((g,IntSyn.id), (IntSyn.Null, IntSyn.Null, 0, 0),
			  scInit)) handle Done => ();
			    (* printing is timed into solving! *)
			Trail.reset ();	(* in case Done was raised *)
		        checkSolutions (expected, try, !solutions))
		else if !Global.chatter >= 3
		       then TextIO.print ("Skipping query (bound = 0)\n")
		     else if !Global.chatter >= 2
			    then TextIO.print ("skipping")
			  else ();
		if !Global.chatter >= 3
		  then TextIO.print "____________________________________________\n\n"
		else if !Global.chatter >= 2
		       then TextIO.print (" OK\n")
		     else ();
                install s'
              end

	    | install' (S.Cons(Parser.FixDecl ((name,r),fixity), s')) =
		(Names.installFixity (name, fixity)
		 handle Names.Error (msg) => raise Names.Error (wrapRegion(r,msg));
		 install s')
	    | install' (S.Cons(Parser.NamePref ((name,r), namePref), s')) =
		(Names.installNamePref (name, namePref)
		 handle Names.Error (msg) => raise Names.Error (wrapRegion(r,msg));
		install s')
	    | install' (S.Cons(Parser.ModeDecl mterm, s')) =
		(Modes.installMode (ModeRecon.modeToMode mterm);
		 install s')
	    | install' (S.Cons(Parser.LexDecl lterm, s')) =
		(Lex.install (LexRecon.termToTerm lterm);
		 install s')
	in
	  install (Parser.parseFile instream)
	end)

  fun compile () = (Index.compile ();
		    Compile.compile ();
		    compiled := true)

  fun qLoop () = qLoops (Parser.parseQuery ("?- ", "   "))
  and qLoops (s) = qLoops' ((Timers.time Timers.parsing S.expose) s)
  and qLoops' (S.Empty) = OK
    | qLoops' (S.Cons (query, s')) =
      let
	val (A, Xs) = TpReconQ.termToQuery(query) (* times itself *)
	val g = (Timers.time Timers.compiling Compile.compileGoal) A
	fun scInit M =
	    (linCheckAnswer Xs ;
	     TextIO.print ((Timers.time Timers.printing evarInstToString) Xs ^ "\n");
	     if !Global.chatter >= 3
	       then TextIO.print ((Timers.time Timers.printing evarInstToString) [(M, "%P")] ^ "\n")
	     else ();
	     Constraints.warnConstraints (Names.evarCnstr ());
	     if moreSolutions () then () else raise Done)
	val _ = if !Global.chatter >= 3
		  then TextIO.print "Solving...\n"
		else ()
      in
	((Timers.time Timers.solving AbsMachine.solve)
	 ((g,IntSyn.id), (IntSyn.Null, IntSyn.Null, 0, 0), scInit);
	     (* scInit is timed into solving! *)
	 TextIO.print "No more solutions\n")
	handle Done => ();
	(* Ignore s': parse one query at a time *)
	qLoop ()
      end

  fun topLoop () = case (handleExceptions "stdIn" qLoop) ()
                     of ABORT => topLoop ()
                      | OK => ()

  fun top () = (Index.reset (); CompSyn.sProgReset ();
		compiled := false;
		if !Global.chatter >= 3
		  then TextIO.print ("Compiling...")
		else ();
		compile ();
		if !Global.chatter >= 3
		  then TextIO.print ("Done\n")
		else ();
		topLoop ())

  fun reset () = (IntSyn.sgnReset (); Names.reset (); Modes.reset ();
		  Index.reset (); CompSyn.sProgReset ();
		  compiled := false)

  type config = string list
  fun defineConfig (files) = files

  fun readAbort (filename, OK) = readFile (filename)
    | readAbort (_, ABORT) = ABORT

  fun readConfig (config) =
      (reset ();
       List.foldl readAbort OK config)

  fun compileConfig (config) =
      (reset ();
       case List.foldl readAbort OK config
	 of OK => (compile (); OK)
	  | ABORT => ABORT)

end; (* functor FrontEnd *)
