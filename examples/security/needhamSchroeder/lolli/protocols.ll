MODULE protocols.

run :- 
	hook T,
	display T.

hook T :- step T.

display ((out X) :: T)
	:- write X,nl,
	   display T.
display nil :- nl.


annKey alice.
annKey bob.
annKey intruder.

memKey (inv intruder).

LINEAR sessionA (s z).

LINEAR sessionB (s z).
