(* Printer for Lexical Termination Declarations *)
(* Author: Carsten Schuermann *)

functor LexPrint (structure LexSyn' : LEXSYN
		    structure Formatter : FORMATTER)
  : LEXPRINT
  (* :> LEXPRINT where LexSyn = LexSyn' *) =
struct
  structure LexSyn = LexSyn'
    
  local
    structure L = LexSyn
    structure I = L.IntSyn
    structure F = Formatter
      
    fun fmtIds nil = []
      | fmtIds (n :: nil) = [F.String (n)] 
      | fmtIds (n :: L) = [F.String (n), F.String " "] @ (fmtIds L)
      
    fun fmtParams nil = []
      | fmtParams (SOME n :: nil) = [F.String (n)]
      | fmtParams (NONE :: nil) = [F.String ("_")]
      | fmtParams (SOME n :: L) = [F.String (n), F.String " "] @ (fmtParams L)
      | fmtParams (NONE :: L) = [F.String ("_"), F.String " "] @ (fmtParams L)

    fun fmtType (c, L) = F.HVbox ([F.String (I.entryName (I.sgnLookup c)), F.String " "] @ (fmtParams L))
      
    fun fmtBody nil = []
      | fmtBody (T :: nil) = [F.String "(", fmtType T, F.String ")"]
      | fmtBody (T :: L) = [F.String "(", fmtType T, F.String ") "] @ (fmtBody L)
      
    fun fmtTerm (L.Body L) = fmtBody L
      | fmtTerm (L.Pi (L, T)) = ([F.String "{", F.HVbox (fmtIds L), F.String "} "] @ (fmtTerm T))

    fun termToString T = F.makestring_fmt (F.HVbox (fmtTerm T))
  in
    val termToString = termToString
  end (* local *)

end (* functor LexPrint *)
