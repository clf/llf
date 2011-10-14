MODULE ns.

not G :- G -> fail | true.


tMsg 1 (crypt (pair (a2m X) (k2m K1)) K2).
tMsg 2 (crypt (pair (a2m X1) (a2m X2)) K).
tMsg 3 (crypt (a2m X) K).


% Alice's Role

%LINEAR
%step ((out (nsA11 A B)) :: T)
%	:- attack nsA A,
%           not (A = intruder),
%	   sessionA (s N),
%	   annKey B,
%	   not (B = A),
%           not (B = intruder),
%write_sans "nsA11 ",write A, write_sans " ", write B,nl,
%	   (forall Na \
%	         a1 A B Na
%	      -o sessionA N
%	      -o attacked A Na
%	      -o toNet 1 (crypt (pair (a2m Na) (k2m A)) B)
%	      -o transit T).

step ((out (nsA1 A B)) :: T)
	:- sessionA (s N),
	   annKey A,
	   annKey B,
	   not (A = B),
%write_sans "nsA1 ",write A, write_sans " ", write B,nl,
	   (forall Na \
	         a1 A B Na
	      -o sessionA N
	      -o toNet 1 (crypt (pair (a2m Na) (k2m A)) B)
	      -o transit T).

step ((out (nsA2 A B)) :: T)
	:- a1 A B X,
           fromNet 2 (crypt (pair (a2m X) (a2m Y)) A),
%write_sans "nsA2 ",write A, write_sans " ", write B,nl,
           (     a2 A B X Y
	      -o toNet 3 (crypt (a2m Y) B)
	      -o transit T).

% Bob's Role

LINEAR
%step ((nsB11 A B) :: T)
%	:- attack nsB B,
%	   not (B = intruder),
%	   sessionB (s N),
%	   fromNet 1 (crypt (pair (a2m X) (k2m A)) B)
%	   annKey A,
%	   not (A = B),
%           not (A = intruder),
%write_sans "nsB11 ",write A, write_sans " ", write B,nl,
%	   (forall Nb \
%	         b1 B A X Nb
%	      -o sessionB N
%	      -o attacked B Nb
%	      -o toNet 2 (crypt (pair (a2m X) (a2m Nb)) A)
%	      -o transit T).

step ((out (nsB1 A B)) :: T)
	:- sessionB (s N),
	   annKey B,
	   fromNet 1 (crypt (pair (a2m X) (k2m A)) B),
	   annKey A,
	   not (B = A),
%write_sans "nsB1 ",write A, write_sans " ", write B,nl,
	   (forall Nb \
	         b1 B A X Nb
	      -o sessionB N
	      -o toNet 2 (crypt (pair (a2m X) (a2m Nb)) A)
	      -o transit T).

step ((out (nsB2 A B)) :: T)
	:- b1 B A X Y,
           fromNet 3 (crypt (a2m Y) B),
%write_sans "nsB2 ",write A, write_sans " ", write B,nl,
           (     b2 B A X Y
	      -o step T).


% Termination condition

step ((out T) :: nil)
	:- a2 A1 B1 Na1 Nb1,
	   b2 B2 A2 Na2 Nb2,
	   fooled Na1 Na2 Nb1 Nb2 A1 A2 B1 B2 T,
	   erase.

fooled Na Na Nb Nb A A B B ok
	:- noattack.

fooled Na Na Nb Nb A1 A2 B1 B2 fooledA
	:- attacked A1 Na,
	   not (B1 = B2).

fooled Na Na Nb Nb A A B1 B2 fooledB
	:- attacked B2 Nb,
	   not (A1 = A2).
