(* Lexical Termination Declarations *)
(* Author: Carsten Schuermann *)

functor LexSyn (structure IntSyn' : INTSYN)
  : LEXSYN
  (* :> LEXSYN where IntSyn = IntSyn' *) =
struct
  structure IntSyn = IntSyn'

  type Param = IntSyn.name option

  datatype Term = 
    Pi of IntSyn.name list * Term
  | Body of (IntSyn.cid * Param list) list
 
end; (* functor LexSyn *)

