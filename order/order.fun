(* Terminiation Order *)
(* Author: Carsten Schuermann *)

functor Order (structure IntSyn' : INTSYN
	       structure Table : TABLE where type key = int)
  : ORDER
  (* :> ORDER where IntSyn = IntSyn' *) = 
struct
  structure IntSyn = IntSyn'

  exception Error of string

  datatype Selector =			(* Selector for lex ordering  *)
      Nil				(* S ::= .                    *)
    | Select of int * Selector          (*     | member ord, S        *)

  datatype Mutual =			(* Termination ordering       *)
      Empty				(* O ::= Empty                *)
    | LE of IntSyn.cid * Mutual		(*     | less equal           *)
    | LT of IntSyn.cid * Mutual		(*     | less than            *)

  datatype Order = 
      Order of Selector * Mutual
 
  local
    structure I = IntSyn
    val OrderTable : Order Table.Table = Table.new(0);
    
    fun reset () = Table.clear OrderTable
    fun install (cid, O) = Table.insert OrderTable (cid, O)
    fun lookup cid =  
      case (Table.lookup OrderTable cid) of 
	NONE => raise Error ("No order assigned for " ^ (I.entryName (I.sgnLookup cid)))
      | SOME O => O
	  
    fun mutual c = 
      let
	fun mutual' (Empty, A) = A
	  | mutual' (LE (c, M), A) = mutual' (M, c :: A)
	  | mutual' (LT (c, M), A) = mutual' (M, c :: A)
	val Order (_, M) = lookup c
      in
	mutual' (M, nil)
      end

    fun transClosure (nil, A) = A
      | transClosure (c :: C, A) =
          if List.exists (fn c' => c = c') A then transClosure (C, A)
	  else transClosure ((mutual c) @ C, c ::A)

  in
    val reset = reset
    val install = install
    val lookup = lookup
    val closure = fn c => transClosure ([c], nil)
  end (* local *)
end; (* functor Order *)
