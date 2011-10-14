(* Lexical Termination Declarations *)
(* Author: Carsten Schuermann *)

functor Lex (structure Global : GLOBAL
	     structure LexSyn': LEXSYN
	     structure Order : ORDER
	       sharing Order.IntSyn = LexSyn'.IntSyn
	     structure LexPrint : LEXPRINT
	       sharing LexPrint.LexSyn = LexSyn')
  : LEX
  (* :> LEX where LexSyn = LexSyn' *) =
struct
  structure LexSyn = LexSyn'

  exception Error of string

  local
    structure L = LexSyn
    structure I = L.IntSyn
    structure P = LexPrint
    structure O = Order

    fun calculateMutual (nil, k, A) = A
      | calculateMutual ((c, _) :: L, k, A) =
          calculateMutual (L, k, k (c, A))

    fun checkExplicit (G, (I.Uni I.Type, nil)) = ()
      | checkExplicit (G, (I.Pi (_, V), xOpt :: L)) = 
          checkExplicit (G, (V, L))
      | checkExplicit _ = raise Error "wrong number of arguments supplied"

    fun checkImplicit (0, V, k) = k V
      | checkImplicit (n, I.Pi (_, V), k) = checkImplicit (n-1, V, k)

    fun notExists (x, nil) = ()
      | notExists (x, NONE :: L) =
          notExists (x, L)
      | notExists (x, SOME x' :: L) = 
        if x = x' then raise Error "variable name not expected"
	else notExists (x, L)

    fun notSelectNames (nil, L) = ()
      | notSelectNames (x :: N, L) = 
          (notExists (x, L); notSelectNames (N, L))

    fun exists (x, n, nil) = NONE
      | exists (x, n, NONE :: L) = 
          exists (x, n+1, L)
      | exists (x, n, SOME x' :: L) = 
          if x = x' then (notExists (x, L); SOME n)
	  else exists (x, n+1, L)

    fun selectNames (N', nil, n, L, P) = (N', O.Nil)
      | selectNames (N', x::N, n, L, P) = 
        case exists (x, n, L) of
	  NONE => selectNames (x::N', N, n, L, P)
	| SOME n' => (notSelectNames (N', L); (N' @ N, O.Select (n', P)))

    fun select (I.Null, n, L, P) = (I.Null, P)
      | select (I.Decl (G, N), n, L, P) =
        let 
	  val (N', P') = selectNames (nil, N, n, L, P)
	  val (G'', P'') = select (G, n, L, P')
	in
	  (I.Decl (G'', N'), P'') 
	end

    fun calculateSelector (G, (c, L)) =
        let 
	  val n = I.constImp c
	  val V = I.constType c
	  val _ = checkImplicit (n, V, fn V' => checkExplicit (G, (V', L)))
	in
	  select (G, n+1, L, O.Nil)
	end

    fun emptyCtx (I.Null) = ()
      | emptyCtx (I.Decl (G, nil)) = 
          emptyCtx G
      | emptyCtx _ = raise Error "Unused declared variables: Typo?"

    fun installBody (G, L', nil) = emptyCtx G
      | installBody (G, L', (B as (c, _)):: L) =
        let 
	  val (G', S') = calculateSelector (G, B)
	  val M' = calculateMutual (L, fn cM' => O.LE cM',
				    calculateMutual (B :: L', fn cM' => O.LT cM', O.Empty))
	  val _ = O.install (c, O.Order (S', M'))
	in
	  installBody (G', B :: L', L)
	end

    fun installTerm (G, L.Body nil) =
	  raise Error "type expected, nothing found"
      | installTerm (G, L.Body L) =
          installBody (G, nil, L)   
      | installTerm (G, L.Pi (L, T)) = 
          installTerm (I.Decl (G, L), T)
      
    fun install T = 
      (installTerm (I.Null, T);
       if !Global.chatter >= 3 
	 then TextIO.print ("%lex " ^ (P.termToString T) ^ ".\n")
       else ())
		 
  in
    val install = install
  end (* local *)

end (* functor Lex *)
