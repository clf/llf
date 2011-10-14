(* Parsing Lex Declarations *)
(* Author: Carsten Schuermann *)

functor ParseLex
  (structure Parsing' : PARSING
   structure LexSynExt' : LEXSYNEXT
   structure Paths : PATHS)
     : PARSE_LEX
  (* :> PARSE_LEX
        where Parsing = Parsing'
        where LexSynExt = LexSynExt'
  *) =
struct
  structure Parsing = Parsing'
  structure LexSynExt = LexSynExt'

  local
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  
    structure E = LexSynExt
    structure P = Paths

    fun stripRBrace (LS.Cons ((L.RBRACE, r), s')) = LS.expose s'
      | stripRBrace (LS.Cons ((t, r), _))  = 
          Parsing.error (r, "Expected `}', found " ^ L.toString t)

    fun stripRParen (LS.Cons ((L.RPAREN, r), s')) = LS.expose s'
      | stripRParen (LS.Cons ((t, r), _))  = 
          Parsing.error (r, "Expected `)', found " ^ L.toString t)


    fun parseIds (LS.Cons ((L.ID (_, id), r), s')) =
        let 
	  val (idL, f') = parseIds (LS.expose s') 
	in 
	  (id :: idL, f')
	end
      | parseIds f = (nil, f)
	

    fun parseParams (LS.Cons ((L.ID (_, id), r), s')) =
        let 
	  val (idL, f') = parseParams (LS.expose s') 
	in 
	  (SOME id :: idL, f')
	end
      | parseParams (LS.Cons ((L.UNDERSCORE, r), s')) =
        let 
	  val (idL, f') = parseParams (LS.expose s') 
	in 
	  (NONE :: idL, f')
	end
      | parseParams f = (nil, f)
	
    fun parseType (LS.Cons ((L.ID (_, id), r), s')) =
        let 
	  val (T, f' as LS.Cons ((_ ,r'), _)) = parseParams (LS.expose s')
	in
	  ((id, T, P.join (r, r')), f')
	end
      
    fun parseBody (f as LS.Cons ((L.DOT, r), s')) =
        (nil, f)
      | parseBody (LS.Cons ((L.LPAREN, r), s')) = 
        let 
	  val (t, f') = parseType (LS.expose s')
	  val (tl, f'') = parseBody (stripRParen f')
	in
	  (t :: tl, f'')
	end
      | parseBody f = 
	let 
	  val (t, f') = parseType f
	in
	  (t :: nil, f')
	end
    fun parseTerm (LS.Cons ((L.LBRACE, r), s')) = 
        let 
	  val (idL, f') = parseIds (LS.expose s')
	  val f'' = stripRBrace f'
	  val (t''', f''' as LS.Cons ((_, r'), _)) = parseTerm f''
	in
	  (E.pi (idL, t'''), f''')
	end
      | parseTerm f = 
	let 
	  val (t', f') = parseBody f
	in
	  (E.body t', f')
	end

    fun parseLex' (LS.Cons ((L.LEX, r), s')) = 
          parseTerm (LS.expose s')

  in
    val parseLex' = parseLex'
  end  (* local ... in *)

end;  (* functor Parser *)



