(* Parsing Signature Entries *) 
(* Author: Frank Pfenning *)

functor ParseEntry
  (structure Parsing' : PARSING
   structure ExtSyn' : EXTSYN
   structure ParseTerm : PARSE_TERM
     sharing ParseTerm.Parsing = Parsing'
     sharing ParseTerm.ExtSyn = ExtSyn')
     : PARSE_ENTRY
  (* :> PARSE_ENTRY
        where Parsing = Parsing'
        where ExtSyn = ExtSyn'
  *) =
struct

  structure Parsing = Parsing'
  structure ExtSyn = ExtSyn'

  local
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  

    fun parseSgnEntry3 (name, tm, s) =
        let
	  val (tm', f') = ParseTerm.parseTerm' (LS.expose s)
	in
	  (ExtSyn.cdefn (name, tm', tm), f')
	end

    fun parseSgnEntry2 (name, (tm, LS.Cons((L.EQUAL, r), s'))) =
          parseSgnEntry3 (name, tm, s')
      | parseSgnEntry2 (name, (tm, f)) =
	  (ExtSyn.cdecl (name, tm), f)

    fun parseSgnEntry1 (name, LS.Cons ((L.COLON, r), s')) =
          parseSgnEntry2 (name, ParseTerm.parseTerm' (LS.expose s'))
(*      | parseSgnEntry1 (name, LS.Cons ((L.HAT, r), s')) =
	  Parsing.error (r, "Linear declarations not supported yet")  *)
      | parseSgnEntry1 (name, LS.Cons ((L.HAT, r), s')) =
	  let
	    val (tm, f) = ParseTerm.parseTerm' (LS.expose s')
	  in
	    (ExtSyn.lcdecl (name, tm), f)
	  end
      | parseSgnEntry1 (name, LS.Cons ((L.EQUAL, r), s')) =
	  parseSgnEntry3 (name, ExtSyn.omittyp r, s')
      | parseSgnEntry1 (name, LS.Cons ((t,r), s')) =
	  Parsing.error (r, "Expected `:', `^', or `=', found " ^ L.toString t)

    (* parseSngEntry' : lexResult front -> ExtSyn.sgnentry * lexResult front
       Invariant: first token in exposed input stream is an identifier
    *)
    fun parseSgnEntry' (LS.Cons ((L.ID (idCase,name), r), s')) =
          parseSgnEntry1 (name, LS.expose s')

    (* parseSgnEntry --- currently not exported *)
    fun parseSgnEntry (s) = parseSgnEntry' (LS.expose s)
      
  in
    val parseSgnEntry' = parseSgnEntry'
  end  (* local ... in *)

end;  (* functor ParseEntry *)
