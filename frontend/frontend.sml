(* Front End Interface *)
(* Author: Frank Pfenning *)

(* Presently, we do not memoize the token stream returned *)
(* by the lexer.  Use Stream = MStream below if memoization becomes *)
(* necessary. *)
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);

structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);

(*
structure ExtInt = ExtInt (structure IntSyn' = IntSyn);
*)

structure Timers =
  Timers (structure Timing' = Timing);


structure FVars =
  FVars (structure IntSyn' = IntSyn
         structure Names = Names);

structure EVars =
  EVars (structure IntSyn' = IntSyn
         structure Names = Names
         structure Table = StringRedBlackTree);


structure TpRecon =
  TpRecon (structure Global = Global
	   structure IntSyn' = IntSyn
	   structure Names = Names
	   structure Paths' = Paths
 	   structure Whnf = Whnf
	   structure Normalize = Normalize
	   structure Pattern = Pattern
	   structure Unify = Unify
	   structure Abstract = Abstract
	   structure TypeCheck = TypeCheck
	   structure LinCheck = LinCheck
	   structure Strictness = Strictness
	   structure IPrint = IPrint
	   structure EPrint = EPrint
	   structure Timers = Timers
           structure Vars = FVars);

structure TpReconQ =
  TpRecon (structure Global = Global
	   structure IntSyn' = IntSyn
	   structure Names = Names
	   structure Paths' = Paths
 	   structure Whnf = Whnf
	   structure Normalize = Normalize
	   structure Pattern = Pattern
	   structure Unify = Unify
	   structure Abstract = Abstract
	   structure TypeCheck = TypeCheck
	   structure LinCheck = LinCheck
	   structure Strictness = Strictness
	   structure IPrint = IPrint
	   structure EPrint = EPrint
	   structure Timers = Timers
           structure Vars = EVars);

structure ModeRecon =
  ModeRecon (structure Global = Global
	     structure IntSyn = IntSyn
	     structure Modes' = Modes
	     structure Pattern = Pattern
	     structure Paths' = Paths
	     structure IModePrint = IModePrint
	     structure EModePrint = EModePrint
	     structure TpRecon' = TpRecon
	     structure Unify = Unify)

structure LexRecon =
  LexRecon (structure Global = Global
	    structure LexSyn' = LexSyn
	    structure Names = Names
	    structure Paths' = Paths)

structure ParseTerm =
  ParseTerm (structure Parsing' = Parsing
	     structure ExtSyn' = TpRecon
	     structure Names = Names);

structure ParseTermQ =
  ParseTerm (structure Parsing' = Parsing
	     structure ExtSyn' = TpReconQ
	     structure Names = Names);

structure ParseEntry =
  ParseEntry (structure Parsing' = Parsing
	      structure ExtSyn' = TpRecon
	      structure ParseTerm = ParseTerm);

structure ParseFixity =
  ParseFixity (structure Parsing' = Parsing
	       structure Names' = Names);

structure ParseMode =
  ParseMode (structure Parsing' = Parsing
	     structure ExtModes' = ModeRecon
	     structure Paths = Paths
	     structure ParseTerm = ParseTerm);


structure ParseLex =
  ParseLex (structure Parsing' = Parsing
	    structure LexSynExt' = LexRecon
	    structure Paths = Paths);


structure Parser =
  Parser (structure Parsing' = Parsing
	  structure Stream' = Stream
	  structure ExtSyn' = TpRecon
	  structure ExtSynQ' = TpReconQ
	  structure Names' = Names
	  structure ExtModes' = ModeRecon
	  structure LexSynExt' = LexRecon
	  structure ParseEntry = ParseEntry
	  structure ParseFixity = ParseFixity
	  structure ParseMode = ParseMode
	  structure ParseLex = ParseLex
          structure ParseTermQ = ParseTermQ);

structure FrontEnd =
  FrontEnd (structure Global = Global
	    structure IntSyn' = IntSyn
	    structure Names = Names
	    structure Modes = Modes
	    structure Lex = Lex
	    structure Lexer = Lexer
	    structure Parsing = Parsing
	    structure Parser = Parser
	    structure TypeCheck = TypeCheck
	    structure Strictness = Strictness
	    structure Constraints = Constraints
	    structure Abstract = Abstract
	    structure ModeRecon = ModeRecon
	    structure LexRecon = LexRecon
	    structure LinCheck = LinCheck
	    structure Origins = Origins
	    structure TpReconQ = TpReconQ
	    structure TpRecon = TpRecon 
	    structure Normalize = Normalize
	    structure Timers = Timers
	    structure Index = Index
            structure CompSyn' = CompSyn
            structure Compile = Compile
	    structure Trail = Trail
            structure AbsMachine = AbsMachine
            structure IPrint = IPrint
            structure EPrint = EPrint
            structure Whnf = Whnf);

structure LLF = FrontEnd;