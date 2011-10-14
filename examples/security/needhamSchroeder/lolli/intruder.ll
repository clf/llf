MODULE intruder.

LINEAR numNonc 0.

% Send/Receive message

transit T
        :- toNet C X,
%write_sans "receive ", write X,nl,
           (     dMsg (s z) X
            -o dCounter (s z)
            -o peep T).

peep T
        :- dCounter z,
           tMsg Num M,
           genMsg M,
%write_sans "send ", write M,nl,
           (fromNet Num M -o hook T).


% Composition and decompostion

%peep T :- dMsg N (pair X Y),
%          dCounter N,
%write decompose,nl,
%          (     dMsg N X
%           -o dMsg (s N) Y
%           -o dCounter (s N)
%           -o peep T).

%genMsg (pair X Y)
%       :- genMsg X,
%          genMsg Y.


% Encryption and decryption

%peep T :- memKey (inv K),
%          dMsg N (crypt X K),
%write decrypt,nl,
%          (dMsg N X -o peep T).

%genMsg (crypt X K)
%       :- genMsg X,
%          annKey K,
%          not (intruder = K).

% Atomic information

%peep T :- dMsg (s N) (a2m X),
%          aMsg X,
%          dCounter (s N),
%write nostore,nl,
%          (dCounter N -o peep T).

%peep T :- dMsg (s N) (a2m X),
%          not (aMsg X),
%          dCounter (s N),
%write store,nl,
%          (   dCounter N
%           -o aMsg X
%           => peep T).

%genMsg (a2m X) :- aMsg X.


% Public keys

%peep T :- dMsg (s N) (k2m X),
%          dCounter (s N)
%write pub key,nl,
%          (dCounter N -o peep T).

%genMsg (k2m X) :- annKey X.

%% New nonces

%peep T :- numNonc (s N),
%write new nonce,nl,
%           (forall n \
%              (aMsg n
%           => numNonc N
%           -o peep T)).


% Unknown keys

peep T  :- dMsg (s N) (crypt X K),
           not (intruder = K),
           dCounter (s N),
%write forward,nl,
           (   dCounter N
            -o xMsg (crypt X K)
            => peep T).

genMsg (crypt X K)
        :- xMsg (crypt X K),
           not (intruder = K).