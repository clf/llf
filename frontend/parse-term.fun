(* Parsing Terms and Declarations *)
(* Author: Frank Pfenning *)

functor ParseTerm
  (structure Parsing' : PARSING
   structure ExtSyn' : EXTSYN
   structure Names : NAMES)
     : PARSE_TERM
  (* :> PARSE_TERM
        where Parsing = Parsing'
        where ExtSyn = ExtSyn'
  *) =
struct

  structure Parsing = Parsing'
  structure ExtSyn = ExtSyn'

  local
    (* some shorthands *)
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  
    structure Paths = Parsing.Lexer.Paths
    structure FX = Names.Fixity

    (* Operators and atoms for fixity parsing *)
    datatype 'a operator =
        Atom of 'a
      | Infix of (FX.precedence * FX.associativity) * ('a * 'a -> 'a)
      | Prefix of FX.precedence * ('a -> 'a)
      | Postfix of FX.precedence * ('a -> 'a)

    (* Predeclared infix/prefix operators *)
    val fstOp = Prefix (FX.projPrec, ExtSyn.first)
    val sndOp = Prefix (FX.projPrec, ExtSyn.second)
    val juxOp = Infix ((FX.appPrec, FX.Left), ExtSyn.app) (* juxtaposition *)
    val linAppOp = Infix ((FX.appPrec, FX.Left), ExtSyn.linapp)
    (* Abstractions have precedence FX.absPrec *)
    val withOp = Infix ((FX.withPrec, FX.Right), ExtSyn.witH)
    val arrowOp = Infix ((FX.arrowPrec, FX.Right), ExtSyn.arrow)
    val backArrowOp = Infix ((FX.arrowPrec, FX.Left), ExtSyn.backarrow)
    val lolliOp =  Infix ((FX.arrowPrec, FX.Right), ExtSyn.lolli)
    val backLolliOp = Infix ((FX.arrowPrec, FX.Left), ExtSyn.backlolli)
    val pairOp = Infix ((FX.pairPrec, FX.Right), ExtSyn.pair)
    val colonOp = Infix ((FX.colonPrec, FX.Left), ExtSyn.hastype)
    (* Dependent types have precedence FX.piPrec *)

    fun infixOp (infixity, tm) =
          Infix (infixity, (fn (tm1, tm2) =>
			       ExtSyn.app (ExtSyn.app (tm, tm1), tm2)))
    fun prefixOp (prec, tm) =
          Prefix (prec, (fn tm1 => ExtSyn.app (tm, tm1)))
    fun postfixOp (prec, tm) =
          Postfix (prec, (fn tm1 => ExtSyn.app (tm, tm1)))

    fun idToTerm (L.Lower, name, r) = ExtSyn.lcid (name, r)
      | idToTerm (L.Upper, name, r) = ExtSyn.ucid (name, r)
      | idToTerm (L.Quoted, name, r) = ExtSyn.quid (name, r)

    fun isQuoted (L.Quoted) = true
      | isQuoted _ = false

    type stack = (ExtSyn.term operator) list
    type opr = ExtSyn.term operator

    (* The next section deals generically with fixity parsing          *)
    (* Because of juxtaposition, it is not clear how to turn this      *)
    (* into a separate module without passing a juxtaposition operator *)
    (* into the shift and resolve functions                            *)

    structure P :>
      sig
	val reduce : stack -> stack
        val reduceAll : Paths.region * stack -> ExtSyn.term
        val shiftAtom : Paths.region * ExtSyn.term * stack -> stack
        val shift : Paths.region * opr * stack -> stack
        val resolve : Paths.region * opr * stack -> stack
      end =
    struct
      (* Stack invariants, refinements of operator list *)
      (*
	 <p>       ::= <pStable> | <pRed>
	 <pStable> ::= <pAtom> | <pOp?>
	 <pAtom>   ::= Atom _ :: <pOp?>
	 <pOp?>    ::= nil | <pOp>
	 <pOp>     ::= Infix _ :: <pAtom> :: <pOp?>
		     | Prefix _ :: <pOp?>
	 <pRed>    ::= Postfix _ :: Atom _ :: <pOp?>
		     | Atom _ :: <pOp>
      *)
      (* val reduce : <pRed> -> <p> *)
      fun reduce (Atom(tm2)::Infix(_,con)::Atom(tm1)::p') =
	     Atom(con(tm1,tm2))::p'
	| reduce (Atom(tm)::Prefix(_,con)::p') = Atom(con(tm))::p'
	| reduce (Postfix(_,con)::Atom(tm)::p') = Atom(con(tm))::p'
	(* no other cases should be possible by stack invariant *)

      (* val reduceRec : <pStable> -> ExtSyn.term *)
      fun reduceRec (Atom(e)::nil) = e
	| reduceRec (p) = reduceRec (reduce p)

      (* val reduceAll : <p> -> ExtSyn.term *)
      fun reduceAll (r, Atom(e)::nil) = e
        | reduceAll (r, Infix _::p') = Parsing.error (r, "Incomplete infix expression")
	| reduceAll (r, Prefix _::p') = Parsing.error (r, "Incomplete prefix expression")
	| reduceAll (r, nil) = Parsing.error (r, "Empty expression")
	| reduceAll (r, p) = reduceRec (reduce p)

      (* val shift : Paths.region * opr * <pStable> -> <p> *)
      fun shift (r, opr as Atom _, p as (Atom _::p')) =
	    (* insert juxOp operator and reduce *)
	    (* juxtaposition binds most strongly *)
	    reduce (opr::juxOp::p)
	(* Atom/Infix: shift *)
	(* Atom/Prefix: shift *)
	(* Atom/Postfix cannot arise *)
	(* Atom/Empty: shift *)
	(* Infix/Atom: shift *)
	| shift (r, Infix _, Infix _::p') =
	    Parsing.error (r, "Consective infix operators")
	| shift (r, Infix _, Prefix _::p') =
	    Parsing.error (r, "Infix operator following prefix operator")
	(* Infix/Postfix cannot arise *)
	| shift (r, Infix _, nil) =
	    Parsing.error (r, "Leading infix operator")
	| shift (r, opr as Prefix _, p as (Atom _::p')) =
	   (* insert juxtaposition operator *)
	   (* will be reduced later *)
	   opr::juxOp::p
	(* Prefix/{Infix,Prefix,Empty}: shift *)
	(* Prefix/Postfix cannot arise *)
	(* Postfix/Atom: shift, reduced immediately *)
	| shift (r, Postfix _, Infix _::p') =
	    Parsing.error (r, "Postfix operator following infix operator")
	| shift (r, Postfix _, Prefix _::p') =
	    Parsing.error (r, "Postfix operator following prefix operator")
	(* Postfix/Postfix cannot arise *)
	| shift (r, Postfix _, nil) =
	    Parsing.error (r, "Leading postfix operator")
	| shift (r, opr, p) = opr::p

      (* val resolve : Paths.region * opr * <pStable> -> <p> *)
      (* Decides, based on precedence of opr compared to the top of the
         stack whether to shift the new operator or reduce the stack
      *)
      fun resolve (r, opr as Infix((prec, assoc), _),
		     p as (Atom(_)::Infix((prec', assoc'), _)::p')) =
	  (case (Int.compare(prec,prec'), assoc, assoc')
	     of (GREATER,_,_) => shift(r, opr, p)
	      | (LESS,_,_) => resolve (r, opr, reduce(p))
	      | (EQUAL, FX.Left, FX.Left) => resolve (r, opr, reduce(p))
	      | (EQUAL, FX.Right, FX.Right) => shift(r, opr, p)
	      | _ => Parsing.error (r, "Ambiguous: infix following infix of identical precedence"))
	| resolve (r, opr as Infix ((prec, assoc), _),
		     p as (Atom(_)::Prefix(prec', _)::p')) =
	  (case Int.compare(prec,prec')
	     of GREATER => shift(r, opr, p)
	      | LESS => resolve (r, opr, reduce(p))
	      | EQUAL => Parsing.error (r, "Ambiguous: infix following prefix of identical precedence"))
	(* infix/atom/atom cannot arise *)
	(* infix/atom/postfix cannot arise *)
	(* infix/atom/<empty>: shift *)

	(* always shift prefix *)
	| resolve (r, opr as Prefix _, p) =
	    shift(r, opr, p)

	(* always reduce postfix, possibly after prior reduction *)
	| resolve (r, opr as Postfix(prec, _),
		     p as (Atom _::Prefix(prec', _)::p')) =
	    (case Int.compare(prec,prec')
	       of GREATER => reduce (shift (r, opr, p))
		| LESS => resolve (r, opr, reduce (p))
		| EQUAL => Parsing.error (r, "Ambiguous: postfix following prefix of identical precedence"))
	(* always reduce postfix *)
	| resolve (r, opr as Postfix(prec, _),
		     p as (Atom _::Infix((prec', _), _)::p')) =
	    (case Int.compare(prec,prec')
	       of GREATER => reduce (shift (r, opr, p))
		| LESS => resolve (r, opr, reduce (p))
		| EQUAL => Parsing.error (r, "Ambiguous: postfix following infix of identical precedence"))
	| resolve (r, opr as Postfix _, p as (Atom _::nil)) =
	    reduce (shift (r, opr, p))

	(* default is shift *)
	| resolve (r, opr, p) =
	    shift(r, opr, p)

      (* val shiftAtom : term * <pStable> -> <p> *)
      (* does not raise Error exception *)
      fun shiftAtom (r, tm, p as (Atom _::p')) =
	   let
	     val p'' = resolve (r, juxOp, p)
	   in
	     reduce (Atom(tm)::p'')
	   end
	| shiftAtom (r, tm, p) = Atom(tm)::p

    end  (* structure P *)

    (* val parseExp : (L.token * L.region) LS.stream * <p>
                        -> ExtSyn.term * (L.token * L.region) LS.front *)
    fun parseExp (s, p) = parseExp' (LS.expose s, p)

    and parseExp' (LS.Cons((L.ID(idCase,name),r), s), p) =
        let
	  val tm = idToTerm (idCase, name, r)
	in
	  (* Currently, we cannot override fixity status of identifiers *)
	  (* Thus isQuoted always returns false *)
	  if isQuoted (idCase)
	    then parseExp (s, P.shiftAtom (r, tm, p))
	  else case Names.fixityLookup (name)
	         of FX.Nonfix =>
		      parseExp (s, P.shiftAtom (r, tm, p))
	          | FX.Infix infixity =>
		      parseExp (s, P.resolve (r, infixOp (infixity, tm), p))
		  | FX.Prefix (prec) =>
		      parseExp (s, P.resolve (r, prefixOp (prec, tm), p))
		  | FX.Postfix (prec) =>
		      parseExp (s, P.resolve (r, postfixOp (prec, tm), p))
	end
      | parseExp' (LS.Cons((L.UNDERSCORE,r), s), p) =
          parseExp (s, P.shiftAtom (r, ExtSyn.omitobj r, p))
      | parseExp' (LS.Cons((L.TYPE,r), s), p) =
	  parseExp (s, P.shiftAtom (r, ExtSyn.typ r, p))
      | parseExp' (LS.Cons((L.COLON,r), s), p) =
	  parseExp (s, P.resolve (r, colonOp, p))
      | parseExp' (LS.Cons((L.BACKARROW,r), s), p) =
	  parseExp (s, P.resolve (r, backArrowOp, p))
      | parseExp' (LS.Cons((L.ARROW,r), s), p) =
          parseExp (s, P.resolve (r, arrowOp, p))
      | parseExp' (LS.Cons((L.BACKLOLLI,r), s), p) =
	  parseExp (s, P.resolve (r, backLolliOp, p))
      | parseExp' (LS.Cons((L.LOLLI,r), s), p) =
          parseExp (s, P.resolve (r, lolliOp, p))
      | parseExp' (LS.Cons((L.WITH,r), s), p) =
	  parseExp (s, P.resolve (r, withOp, p))
      | parseExp' (LS.Cons((L.TOP,r), s), p) =
	  parseExp (s, P.shiftAtom (r, ExtSyn.top r, p))
      | parseExp' (LS.Cons((L.HAT,r), s), p) =
	  parseExp (s, P.resolve (r, linAppOp, p))
      | parseExp' (LS.Cons((L.COMMA,r), s), p) =
	  parseExp (s, P.resolve (r, pairOp, p))
      | parseExp' (LS.Cons((L.FST,r), s), p) =
	  parseExp (s, P.resolve (r, fstOp, p))
      | parseExp' (LS.Cons((L.SND,r), s), p) =
	  parseExp (s, P.resolve (r, sndOp, p))
      | parseExp' (LS.Cons((L.UNIT,r), s), p) =
	  parseExp (s, P.shiftAtom (r, ExtSyn.unit r, p))
      | parseExp' (LS.Cons((L.LPAREN,r), s), p) =
	  decideRParen (r, parseExp (s, nil), p)
      | parseExp' (f as LS.Cons((L.RPAREN,r), s), p) =
	  (P.reduceAll (r, p), f)
      | parseExp' (LS.Cons((L.LBRACE,r), s), p) =
	  decideRBrace (r, parseDec (s), p)
      | parseExp' (f as LS.Cons((L.RBRACE,r), s), p) =
          (P.reduceAll (r, p), f)
      | parseExp' (LS.Cons((L.LBRACKET,r), s), p) =
          decideRBracket (r, parseDec (s), p)
      | parseExp' (f as LS.Cons((L.RBRACKET,r), s), p) =
	  (P.reduceAll (r, p), f)
      | parseExp' (f as LS.Cons((L.EQUAL,r), s), p) =
	  (P.reduceAll (r, p), f)
      | parseExp' (f as LS.Cons((L.DOT,r), s), p) =
	  (P.reduceAll (r, p), f)
      | parseExp' (f as LS.Cons((L.EOF,r), s), p) =
	  (P.reduceAll (r, p), f)
      | parseExp' (LS.Cons((t,r), s), p) =
	  (* should cover %postfix, %prefix, %infix, %name *)
	  (* possible error recovery: insert DOT *)
	  Parsing.error (r, "Unexpected token " ^ L.toString t
			    ^ " found in expression")

    and parseDec (s) = parseDec' (LS.expose s)
    and parseDec' (LS.Cons ((L.ID (L.Quoted,name), r), s')) =
          (* cannot happen at present *)
	  Parsing.error (r, "Illegal bound quoted identifier " ^ name)
      | parseDec' (LS.Cons ((L.ID (idCase,name), r), s')) =
	(case Names.fixityLookup(name)
	   of FX.Nonfix => parseDec1 (SOME(name), LS.expose s')
	    | FX.Infix _ =>
	       Parsing.error (r, "Cannot bind infix identifier " ^ name)
	    | FX.Prefix _ =>
	       Parsing.error (r, "Cannot bind prefix identifier " ^ name)
            | FX.Postfix _ =>
	       Parsing.error (r, "Cannot bind postfix identifier" ^ name))
      | parseDec' (LS.Cons ((L.UNDERSCORE, r), s')) =
          parseDec1 (NONE, LS.expose s')
      | parseDec' (LS.Cons ((L.EOF, r), s')) =
	  Parsing.error (r, "Unexpected end of stream in declaration")
      | parseDec' (LS.Cons ((t, r), s')) =
	  Parsing.error (r, "Expected variable name, found token "
			    ^ L.toString t)

    and parseDec1 (x, LS.Cons((L.COLON, r), s')) =
        let val (tm, f'') = parseExp (s', nil)
	in (ExtSyn.decl (x, tm), f'') end
      | parseDec1 (x, LS.Cons((L.HAT, r), s')) =
	 parseLinDec (x, r, LS.expose s')
      | parseDec1 (x, f as LS.Cons((L.RBRACE, _), _)) =
          (ExtSyn.decl0 (x), f)
      | parseDec1 (x, f as LS.Cons ((L.RBRACKET, _), _)) =
          (ExtSyn.decl0 (x), f)
      | parseDec1 (x, LS.Cons ((t,r), s')) =
	  Parsing.error (r, "Expected optional type declaration, found token "
			    ^ L.toString (t))

    and parseLinDec (x, r0, f as LS.Cons ((L.RBRACKET, _), _)) =
          (ExtSyn.ldecl0 (x), f)
      | parseLinDec (_, r0, LS.Cons ((L.RBRACE, _), _)) =
	  Parsing.error (r0, "Linear dependent types unsupported")
      | parseLinDec (x, r0, f as LS.Cons((t,_), s')) = 
	  let val (tm, f') = parseExp' (f, nil)
	  in
	    case f'
	        of LS.Cons ((L.RBRACE,r), _)
		    => Parsing.error (Paths.join(r0, r),
				      "Linear dependent types unsupported")
		 | _ => (ExtSyn.ldecl (x, tm), f')
	  end

    and decideRParen (r0, (tm, LS.Cons((L.RPAREN,r), s)), p) =
          parseExp (s, P.shiftAtom(r,tm,p))
      | decideRParen (r0, (tm, LS.Cons((_, r), s)), p) =
	  Parsing.error (Paths.join(r0, r), "Unmatched open parenthesis")

    and decideRBrace (r0, (dec, LS.Cons ((L.RBRACE,r), s)), p) =
          let
	    val piOp = Prefix (FX.piPrec,
			       fn tm => ExtSyn.pi (dec, tm, Paths.join (r0,r)))
	  in
	    parseExp (s, P.resolve (r0, piOp, p))
	  end
      | decideRBrace (r0, (dec, LS.Cons ((_, r), s)), p) =
	  Parsing.error (Paths.join(r0, r), "Unmatched open brace")

    and decideRBracket (r0, (dec, LS.Cons ((L.RBRACKET,r), s)), p) =
          let
	    val lamOp = Prefix (FX.absPrec,
				fn tm => ExtSyn.lam (dec,tm,Paths.join (r0,r)))
	  in
	    parseExp (s, P.resolve (r0, lamOp, p))
	  end
      | decideRBracket (r0, (dec, LS.Cons ((_, r), s)), p) =
	  Parsing.error (Paths.join(r0, r), "Unmatched open bracket")
  in
    val parseTerm' = (fn f => parseExp' (f, nil))
    val parseDec' = parseDec'
  end  (* local ... in *)

end;  (* functor ParseTerm *)
