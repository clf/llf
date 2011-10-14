(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor ParseMode
  (structure Parsing' : PARSING
   structure ExtModes' : EXTMODES
   structure Paths : PATHS
   structure ParseTerm : PARSE_TERM
     sharing ParseTerm.Parsing = Parsing'
     sharing ParseTerm.ExtSyn = ExtModes'.ExtSyn)
     : PARSE_MODE
  (* :> PARSE_MODE
        where Parsing = Parsing'
        where ExtModes = ExtModes'
  *) =
struct
  structure Parsing = Parsing'
  structure ExtModes = ExtModes'

  local
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  
    structure E = ExtModes
    structure P = Paths

    fun extract (s, i) = 
        let
	  val s' = String.substring (s, i, (String.size s)-i)
	in
	  if String.size s' = 0 then NONE else SOME s'
	end

    fun stringToId (r, id) =
        if Char.isUpper (String.sub (id, 0))
	  then id
	else Parsing.error (r, "Expected uppercase variable name, found "
			       ^ "`" ^ id ^ "'")
      
    fun stringToMode (r, id) =
        case String.sub (id, 0)
	  of #"*" => (E.star r, extract (id, 1))
	   | #"-" => (if (String.size id = 1) orelse String.sub (id, 1) <> #"-"
			then (E.minus r, extract(id, 1))
		      else (E.minusminus r, extract(id, 2)))
	   | #"+" => (if (String.size id = 1) orelse String.sub (id, 1) <> #"+"
			then (E.plus r,  extract(id, 1))
		      else (E.plusplus r, extract(id, 2)))
	   | _ => Parsing.error (r, "Expected mode `+', `-', `*', `++', or `--', found " ^ "`" ^ id ^ "'")

    fun validateArg (r, (mode, SOME id)) = (mode, SOME (stringToId (r, id)))
      | validateArg (r, (_, NONE)) = Parsing.error (r, "Missing variable following mode")

    fun validateMode (r, (mode, NONE)) = mode
      | validateMode (r, (_, SOME(id))) = Parsing.error (r, "Expected simple mode, found mode followed by identifier " ^ id) 

    fun parseImplicitSpine (f as LS.Cons ((L.DOT, r), s')) =
	  (E.nilIm r, f)
      | parseImplicitSpine (LS.Cons ((L.ID (_, id), r), s')) =
	let 
	  val mId = validateArg (r, stringToMode (r, id))
	  val (mS', f') = parseImplicitSpine (LS.expose s')
	in 
	  (E.appIm (mId, mS'), f')
	end
      | parseImplicitSpine (LS.Cons ((t, r), s')) =
	  Parsing.error (r, "Expected mode or `.', found " ^ L.toString t)

    fun stripRBrace (LS.Cons ((L.RBRACE, r), s')) = LS.expose s'
      | stripRBrace (LS.Cons ((t, r), _))  = 
          Parsing.error (r, "Expected `}', found " ^ L.toString t)

    and parseExplicit (LS.Cons (t0 as (L.ID (c, id), r0), s'), r1) =
        (* Look ahead one token to decide if quantifier follows *)
	(case LS.expose s'
	   of LS.Cons ((L.LBRACE, r), s'') =>
	      (* found quantifier --- id must be mode *)
	      let 
		val mId = stringToMode (r0, id)
		val m = validateMode (r0, mId)
		val (d', f') = ParseTerm.parseDec' (LS.expose s'')
		val f'' = stripRBrace f'
		val (t', f''') = parseExplicit (f'', r1) 
	      in 
		(E.piEx (m, d', t'), f''')
	      end
	    | LS.Cons TS => 
	      (* no quantifier --- parse atomic type *)
	      let 
		val (t', f' as LS.Cons ((_, r), s')) = 
		    ParseTerm.parseTerm' (LS.Cons (t0, LS.cons TS))
	      in
		(E.rootEx (t', P.join (r, r1)), f')
	      end)
      | parseExplicit (LS.Cons ((t, r), s'), _) =
          Parsing.error (r, "Expected mode or identifier, found " ^ L.toString t)

    (* parseMode2 switches between explicit and implicit mode declarations *)
    fun parseMode2 (lexid, LS.Cons (BS as ((L.LBRACE, r), s')), r1) = 
        let 
	  val (t', f') = parseExplicit (LS.Cons (lexid, LS.cons BS), r1)
	in
	  (E.explicit t', f')
	end
      | parseMode2 ((L.ID (_, name), r), f, _) = 
	let 
	  val (mS', f') = parseImplicitSpine f
	in
	  (E.implicit (E.rootIm (name, r, mS')), f')
	end

    fun parseMode1 (LS.Cons (lexid as (L.ID _, r), s')) = parseMode2 (lexid, LS.expose s', r)
      | parseMode1 (LS.Cons ((t, r), _)) = Parsing.error (r, "Identifier or mode, found " ^ L.toString t)

    (* parseMode' : lexResult front -> termM * lexResult front
       Invariant: exposed input stream starts with MODE
    *)
    fun parseMode' (LS.Cons ((L.MODE, r), s')) = parseMode1 (LS.expose s')
  in
    val parseMode' = parseMode'
  end  (* local ... in *)

end;  (* functor ParseMode *)
