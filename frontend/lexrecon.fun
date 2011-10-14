(* Reconstruct Termination Information *)
(* Author: Carsten Schuermann *)

functor LexRecon (structure Global : GLOBAL
		  structure LexSyn': LEXSYN
		  structure Names : NAMES
		  sharing LexSyn'.IntSyn = Names.IntSyn
		  structure Paths' : PATHS)
  : LEX_RECON
  (* :> LEX_RECON
        where LexSyn = LexSyn'
        where Paths = Paths'
  *) =
struct
  structure LexSyn = LexSyn'
  structure Paths = Paths'

  type term =  unit -> LexSyn.Term
    
  exception Error of string

  local
    structure L = LexSyn
    structure P = Paths

    fun error (r, msg) =
      raise Error (P.toString r ^ " " ^ "Error: " ^ (msg))

    fun convertBody nil = nil
      | convertBody ((name, P, r) :: L) = 
          (case Names.nameLookup name of 
	     NONE => error (r, "type family not defined")
	   | SOME cid => (cid, P) :: (convertBody L))

    fun body L () = L.Body (convertBody L)

    fun pi (L, T) () = L.Pi (L, T ())

    fun termToTerm T = T () 
  in
    val body = body
    val pi = pi
    val termToTerm = termToTerm
  end (* local *)
end (* functor LexRecon *)
