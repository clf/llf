(* Top-Level Parser *)
(* Author: Frank Pfenning *)

functor Parser (structure Parsing' : PARSING
		structure Stream' : STREAM (* result stream *)
		structure ExtSyn' : EXTSYN
		structure ExtSynQ' : EXTSYN
                (* sharing type ExtSynQ'.term = ExtSyn'.term *)
		structure Names' : NAMES
		structure ExtModes' : EXTMODES
		structure LexSynExt' : LEXSYNEXT
		structure ParseEntry : PARSE_ENTRY
		  sharing ParseEntry.Parsing = Parsing'
		  sharing ParseEntry.ExtSyn = ExtSyn'
		structure ParseFixity : PARSE_FIXITY
		  sharing ParseFixity.Parsing = Parsing'
		  sharing ParseFixity.Names = Names' 
                structure ParseMode : PARSE_MODE
		  sharing ParseMode.Parsing = Parsing'
		  sharing ParseMode.ExtModes = ExtModes'
	        structure ParseLex : PARSE_LEX
		  sharing ParseLex.Parsing = Parsing'
		  sharing ParseLex.LexSynExt = LexSynExt'
                structure ParseTermQ : PARSE_TERM 
                  sharing ParseTermQ.Parsing = Parsing'
                  sharing type ParseTermQ.ExtSyn.term = ExtSynQ'.term )
  : PARSER
  (* :> PARSER
        where Parsing = Parsing'
        where Stream = Stream'
        where ExtSyn = ExtSyn'
        where ExtSynQ = ExtSynQ'
        where Names = Names'
        where ExtModes = ExtModes'
        where LexSynExt = LexSynExt'
  *) =
struct

  structure Parsing = Parsing'
  structure Stream = Stream'
  structure ExtSyn = ExtSyn'
  structure ExtSynQ = ExtSynQ'
  structure Names = Names'
  structure ExtModes = ExtModes'
  structure LexSynExt = LexSynExt'

  datatype fileParseResult =
    (* c : A  or  c = M : A *)
      SgnEntry of ExtSyn.sgnentry * ExtSyn.Paths.region
    | FixDecl of (ExtSyn.name * ExtSyn.Paths.region) * Names.Fixity.fixity
    | NamePref of (ExtSyn.name * ExtSyn.Paths.region) * ExtSyn.name  
    | ModeDecl of ExtModes.termM
    | LexDecl of LexSynExt.term
    | Query of int option * int option * ExtSynQ.term (* expected, try, A *)
    (* Further pragmas to be added later here *)

  local
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  

    fun stripDot (LS.Cons((L.DOT, r), s)) = s
      | stripDot (LS.Cons((L.RPAREN, r), s)) =
	  Parsing.error (r, "Unexpected right parenthesis")
      | stripDot (LS.Cons((L.RBRACE, r), s)) =
	  Parsing.error (r, "Unexpected right brace")
      | stripDot (LS.Cons((L.RBRACKET, r), s)) =
	  Parsing.error (r, "Unexpected right bracket")
      | stripDot (LS.Cons ((L.EOF, r), s)) =
	  Parsing.error (r, "Unexpected end of file")
      | stripDot (LS.Cons ((L.EQUAL, r), s)) =
	  Parsing.error (r, "Unexpected `='")
      (* Everything else should be impossible *)

    fun stripOptionalDot (LS.Cons ((L.DOT,r), s)) = s
      | stripOptionalDot f = LS.delay (fn () => f)

    fun parseBound' (LS.Cons ((L.ID (_, "*"), r), s')) = (NONE, s')
      | parseBound' (LS.Cons ((L.ID (_, name), r), s')) =
        ((SOME (L.stringToNat (name)), s')
	 handle Overflow => Parsing.error (r, "Bound too large")
	      | L.NotDigit _ => Parsing.error (r, "Bound neither `*' nor a natural number"))
      | parseBound' (LS.Cons ((t,r), s')) =
	  Parsing.error (r, "Expected bound `*' or natural number, found other token")

    fun parseFile (s) =
          Stream.delay (fn () => parseFile' (LS.expose s))

    (* parseFile' : lexResult front -> fileParseResult front *)
    (* parseFile' switches between various specialized parsers *)
    and parseFile' (f as LS.Cons ((L.ID (idCase,name), r0), s')) =
        let
	  val (entry, f' as LS.Cons((_,r'),_)) = ParseEntry.parseSgnEntry' (f)
	  val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons (SgnEntry (entry, r), parseFile (stripDot f'))
	end

      | parseFile' (LS.Cons ((L.UNDERSCORE, r), s')) =
          Parsing.error (r, "Illegal anonymous constant")
      | parseFile' (LS.Cons ((L.EOF, r), s')) = Stream.Empty
      | parseFile' (f as LS.Cons ((L.INFIX, r), s')) = parseFixity' f
      | parseFile' (f as LS.Cons ((L.PREFIX, r), s')) = parseFixity' f
      | parseFile' (f as LS.Cons ((L.POSTFIX, r), s')) = parseFixity' f
      | parseFile' (f as LS.Cons ((L.NAME, r), s')) =
	let
	  val (namePref, f') = ParseFixity.parseNamePref' f
	in
	  Stream.Cons (NamePref namePref, parseFile (stripOptionalDot f'))
	end
      | parseFile' (LS.Cons((L.QUERY, r), s')) =
        let
	  val (expected, s1) = parseBound' (LS.expose s')
	  val (try, s2) = parseBound' (LS.expose s1)
          val (query, f3) = ParseTermQ.parseTerm' (LS.expose s2)
        in 
          Stream.Cons (Query (expected, try, query), parseFile (stripDot f3))
        end
      | parseFile' (f as LS.Cons ((L.MODE, r), s')) = parseMode' f
      | parseFile' (f as LS.Cons ((L.LEX, r), s')) = parseLex' f
      | parseFile' (LS.Cons ((t,r), s')) =
	  Parsing.error (r, "Expected constant name or pragma keyword, found other token")

    and parseFixity' (f) =
        let
	  val (fdecl, f') = ParseFixity.parseFixity' (f)
	in
	  Stream.Cons (FixDecl fdecl, parseFile (stripOptionalDot f'))
	end

    and parseMode' (f) =
        let
	  val (mdecl, f') = ParseMode.parseMode' (f)
	in
	  Stream.Cons (ModeDecl mdecl, parseFile (stripOptionalDot f'))
	end

    and parseLex' (f) =
        let
	  val (ldecl, f') = ParseLex.parseLex' (f)
	in
	  Stream.Cons (LexDecl ldecl, parseFile (stripOptionalDot f'))
	end

    fun parseQ (s) = Stream.delay (fn () => parseQ' (LS.expose s))
    and parseQ' (f) =
        let
	  val (term, f') = ParseTermQ.parseTerm' (f)
	in
	  Stream.Cons (term, parseQ (stripDot (f')))
	end

  in

    val parseFile = (fn instream => parseFile (L.lexStream (instream)))

    fun parseQuery prompts = parseQ (L.lexTerminal prompts)
        
  end  (* local ... in *)

end;  (* functor Parser *)
