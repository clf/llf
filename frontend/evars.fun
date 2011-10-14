(* Translating Free Identifiers to EVars *)

functor EVars (structure IntSyn' : INTSYN
               structure Names : NAMES
                 sharing Names.IntSyn = IntSyn')
  : VARS
  (* :> VARS where IntSyn = IntSyn' *) =
struct

  structure IntSyn = IntSyn'

  fun var (name, depth) =
      let
	val (X as IntSyn.EVar(_,V,_)) = Names.getEVar name
	val s = IntSyn.Shift depth
      in
	(IntSyn.EClo (V, s),
	 fn S => IntSyn.Redex (IntSyn.EClo (X, s), S))
      end
end;
