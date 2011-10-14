(* Origins of Declarations *)
(* Author: Frank Pfenning *)

functor Origins (structure IntSyn' : INTSYN
		 structure Paths' : PATHS)
  : ORIGINS
  (* :> ORIGINS
        where IntSyn = IntSyn' 
	where Paths = Paths'
  *) =
struct

  structure IntSyn = IntSyn'
  structure Paths = Paths'

  local
    val cidMax = 9999 (* parameter!  coordinate with intsyn.fun *)
    val originArray = Array.array (10000, NONE)
        : Paths.occEntry option Array.array
  in
    fun installOrigin (cid, ocOpt) = Array.update (originArray, cid, ocOpt)
    fun originLookup (cid) = Array.sub (originArray, cid)
  end

end;  (* functor Origins *)
