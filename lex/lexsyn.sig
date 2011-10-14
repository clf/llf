(* Lexical Termination Declarations *)
(* Author: Carsten Schuermann *)

signature LEXSYN =
sig
  structure IntSyn : INTSYN

  type Param = IntSyn.name option

  datatype Term = 
    Pi of IntSyn.name list * Term
  | Body of (IntSyn.cid * Param list) list 

end;
