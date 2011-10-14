(* Translating Free Identifiers to FVars *)

functor FVars (structure IntSyn' : INTSYN
               structure Names : NAMES
                 sharing Names.IntSyn = IntSyn')
  : VARS
  (* :> VARS where IntSyn = IntSyn' *) =
struct

  structure IntSyn = IntSyn'

  fun clearState () = ()

  fun var (name, depth) =
      let
	val V' = Names.getFVarType (name)
	val s = IntSyn.Shift (depth)
      in
        (IntSyn.EClo (V', s),
	 fn S => IntSyn.Root (IntSyn.FVar (name, V', s), S))
      end
end;


