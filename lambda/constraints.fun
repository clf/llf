(* Manipulating Constraints *)
(* Author: Jeff Polakow *)

functor Constraints
    (structure IntSyn' : INTSYN
     structure Conv : CONV
       sharing Conv.IntSyn = IntSyn')
       : CONSTRAINTS
  (* :> CONSTRAINTS where IntSyn = IntSyn' *) =
struct

  structure IntSyn = IntSyn'

  (*
     Constraints cnstr are of the form (X<I>[s] = U).
     Invariants:
       G |- s : G'  G' |- X<I> : V
       G |- U : W
       G |- V[s] == W : L
       (X<>,s) is whnf, but X<>[s] is not a pattern
     If X<I> is uninstantiated, the constraint is inactive.
     If X<I> is instantiated, the constraint is active.

     Constraints are attached directly to the EVar X
     or to a descendent  -fp?
  *)

  (* simplify Eqns = Eqns'
     Effects: simplifies the constraints in Eqns by removing constraints
       of the form U = U' where G |- U == U' : V (mod beta/eta)
       Neither U nor U' needs to be a pattern
  *)
  fun simplify nil = nil
    | simplify ((Eqn as IntSyn.Eqn (U1, U2)) :: Cnstr) =
      if Conv.conv ((U1, IntSyn.id), (U2, IntSyn.id))
	then simplify Cnstr
      else Eqn :: simplify Cnstr

  fun namesToString (name::nil) = name ^ "."
    | namesToString (name::names) = name ^ ", " ^ namesToString names

  fun warnConstraints (nil) = ()
    | warnConstraints (names) = print ("Constraints remain on " ^ namesToString names ^ "\n")

end;  (* functor Constraints *)
