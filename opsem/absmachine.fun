(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

functor AbsMachine (structure IntSyn' : INTSYN
		    structure CompSyn' : COMPSYN
		      sharing CompSyn'.IntSyn = IntSyn'
		    structure Unify : UNIFY
		      sharing Unify.IntSyn = IntSyn'
		    structure Trail : TRAIL
		      sharing Trail.IntSyn = IntSyn'
		    structure CPrint : CPRINT
                      sharing CPrint.IntSyn = IntSyn'
                      sharing CPrint.CompSyn = CompSyn'
		    structure Names : NAMES 
                      sharing Names.IntSyn = IntSyn')
  : ABSMACHINE
  (* :> ABSMACHINE
        where IntSyn = IntSyn'
        where CompSyn = CompSyn'
  *) =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  datatype slack =                 (* Slack indicator / T-flag        *)
    Slack
  | NoSlack

  local
    structure I = IntSyn
    open CompSyn

  in

    (* eraseStrict (dProg) => dProg'
       Invariants:
         If    dProg = (G,dPool,st,lx)
         then  dProg' = (G,dPool',0,lx)
         and for i=1..|dPool|,
	   - dPool'_i = Used r   if dPool_i  = Strict r
           - dPool'_i = dPool_i  otherwise
    *)
    fun eraseStrict (dProg as (G, dPool, 0, lx)) = dProg
      | eraseStrict (G, dPool, st, lx) = 
         let
	   fun eraseStrict' (dPool, 0) = dPool
	     | eraseStrict' (I.Decl (dPool, Strict r), st) =
		I.Decl (eraseStrict' (dPool, st-1), Used r)
	     | eraseStrict' (I.Decl (dPool, cl), st) =
		I.Decl (eraseStrict' (dPool, st), cl)
	 in
	   (G, eraseStrict' (dPool, st), 0, lx)
	 end

    (* eraseStrictCon LC => LC'
       Invariants:
         If    LC = (lCon,st,lx)
         then  LC' = (lCon',st',lx')
         and for i=1..|lCon|,
	   - lCon'_i = (UsedCon,cid)   if lCon_i  = (StrictCon,cid)
           - lCon'_i = lCon_i          otherwise
    *)
    fun eraseStrictCon (LC as (lCon, 0, lx)) = LC
      | eraseStrictCon (lCon, st, lx) = 
         let
	   fun eraseStrictCon' (lCon, 0) = lCon
	     | eraseStrictCon' (I.Decl (lCon, (StrictCon,cid)), st) =
		I.Decl (eraseStrictCon' (lCon, st-1), (UsedCon,cid))
	     | eraseStrictCon' (I.Decl (lCon, lc), st) =
		I.Decl (eraseStrictCon' (lCon, st), lc)
	 in
	   (eraseStrictCon' (lCon, st), 0, lx)
	 end

    (* strictDiff_erase (dProg1,dProg2) => dProg'
       Invariants:
         If    dProg1 = (G, dPool1, st, lx1)
         and   dProg2 = (G, dPool2,  0, lx2)
         and   for i=1..|dPool1|,
	        - if dPool1_i = Strict r, then dPool2_i = Used r
	        - if dPool1_i = Lax r,    then dPool2_i = Lax r or Used r
	        - dPool1_i = dPool2_i     otherwise
         then  dProg' = (G, dPool', st+lx1-lx2, 0)
         and for i=1..|dPool1|,
	   - dPool'_i = Used r    if dPool1_i = Lax r and dPool2_i = Lax _
	   - dPool'_i = Strict r  if dPool1_i = Lax r and dPool2_i = Used _
           - dPool'_i = dPool1_i  otherwise
    *)
    fun strictDiff_erase (dProg1 as (G, dPool1, st1, 0), dProg2) = dProg1
      | strictDiff_erase ((G, dPool1, st1, lx1), (_, dPool2, _, lx2)) =
         let
	   fun sde (dPool1, dPool2, 0) = dPool1
	     | sde (I.Decl (dPool1, Lax r), I.Decl (dPool2, Lax _), lx) =
		I.Decl (sde (dPool1, dPool2, lx-1), Used r)
	     | sde (I.Decl (dPool1, Lax r), I.Decl (dPool2, Used _), lx) =
		I.Decl (sde (dPool1, dPool2, lx-1), Strict r)
	     | sde (I.Decl (dPool1, cl), I.Decl (dPool2, _), lx) =
		I.Decl (sde (dPool1, dPool2, lx), cl)
	 in
	   (G, sde (dPool1, dPool2, lx1), st1 + lx1 - lx2, 0)
	 end

    (* strictConDiff_erase (LC1, LC2) => LC'
       Invariants:
         If    LC1 = (lCon1,st1,lx1)
         and   LC2 = (lCon2,st2,lx2)
         and   |lCon1| = |lCon2|
         and   for i=1..|lCon1|,
	        - if lCon1_i = (StrictCon, cid), then lCon2_i = (UsedCon, cid)
	        - if lCon1_i = (LaxCon, cid),    then lCon2_i = (LaxCon, cid)
	                                                     or (UsedCon, cid)
	        - lCon1_i = lCon2_i              otherwise
         then  LC' = (lCon',st',lx')
         and   |lCon'| = |lCon1|
         and for i=1..|lCon1|,
	   - lCon'_i = (UsedCon, cid)    if  lCon1_i = (LaxCon, cid)
                                         and lCon2_i = (LaxCon,   _)
	   - lCon'_i = (StrictCon, cid)  if  lCon1_i = (LaxCon, cid)
                                         and lCon2_i = (UsedCon,  _)
           - lCon'_i = lCon1_i           otherwise
    *)
    fun strictConDiff_erase (LC1 as (lCon1, st1, 0), LC2) = LC1
      | strictConDiff_erase ((lCon1, st1, lx1), (lCon2, _, lx2)) =
         let
	   fun scde (lCon1, lCon2, 0) = lCon1
	     | scde (I.Decl (lCon1, (LaxCon, cid)),
		     I.Decl (lCon2, (LaxCon,   _)), lx) =
		I.Decl (scde (lCon1, lCon2, lx-1), (UsedCon, cid))
	     | scde (I.Decl (lCon1, (LaxCon, cid)),
		     I.Decl (lCon2, (UsedCon,  _)), lx) =
		I.Decl (scde (lCon1, lCon2, lx-1), (StrictCon, cid))
	     | scde (I.Decl (lCon1, cl), I.Decl (lCon2, _), lx) =
		I.Decl (scde (lCon1, lCon2, lx), cl)
	 in
	   (scde (lCon1, lCon2, lx1), st1 + lx1 - lx2, 0)
	 end

    (* strictDiff_keep (dProg1,dProg2) => dProg'
       Invariants:
         If    dProg1 = (G, dPool1, st, lx1)
         and   dProg2 = (G, dPool2,  0, lx2)
         and   for i=1..|dPool1|,
	        - if dPool1_i = Strict r, then dPool2_i = Used r
	        - if dPool1_i = Lax r,    then dPool2_i = Lax r or Used r
	        - dPool1_i = dPool2_i,    otherwise
         then  dProg' = (G, dPool', st+lx1-lx2, 0)
         and for i=1..|dPool1|,
	   - dPool'_i = Lax r     if dPool1_i = Lax r and dPool2_i = Lax _
	   - dPool'_i = Strict r  if dPool1_i = Lax r and dPool2_i = Used _
           - dPool'_i = dPool1_i  otherwise
    *)
    fun strictDiff_keep (dProg1 as (G, dPool1, st1, 0), dProg2) = dProg1
      | strictDiff_keep ((G, dPool1, st1, lx1), (_, dPool2, _, lx2)) =
         let
	   fun sdk (dPool1, dPool2, 0) = dPool1
	     | sdk (I.Decl (dPool1, cl as Lax _), I.Decl (dPool2, Lax _), lx) =
		I.Decl (sdk (dPool1, dPool2, lx-1), cl)
	     | sdk (I.Decl (dPool1, Lax r), I.Decl (dPool2, Used _), lx) =
		I.Decl (sdk (dPool1, dPool2, lx-1), Strict r)
	     | sdk (I.Decl (dPool1, cl), I.Decl (dPool2, _), lx) =
		I.Decl (sdk (dPool1, dPool2, lx), cl)
	 in
	   (G, sdk (dPool1, dPool2, lx1), st1 + lx1 - lx2, lx2)
	 end

    (* strictConDiff_keep (LC1, LC2) => LC'
       Invariants:
         If    LC1 = (lCon1,st1,lx1)
         and   LC2 = (lCon2,st2,lx2)
         and   |lCon1| = |lCon2|
         and   for i=1..|lCon1|,
	        - if lCon1_i = (StrictCon, cid), then lCon2_i = (UsedCon, cid)
	        - if lCon1_i = (LaxCon, cid),    then lCon2_i = (LaxCon, cid)
                                                             or (UsedCon, cid)
	        - lCon1_i = lCon2_i,             otherwise
         then  LC' = (lCon',st',lx')
         and   |lCon'| = |lCon1|
         and   for i=1..|lCon1|,
	   - lCon'_i = LaxCon cid      if  lCon1_i = (LaxCon, cid)
                                       and lCon2_i = (LaxCon,   _)
	   - lCon'_i = StrictCon cid   if  lCon1_i = (LaxCon, cid)
                                       and lCon2_i = (UsedCon,  _)
           - lCon'_i = lCon1_i         otherwise
    *)
    fun strictConDiff_keep (LC1 as (lCon1, st1, 0), LC2) = LC1
      | strictConDiff_keep ((lCon1, st1, lx1), (lCon2, _, lx2)) =
         let
	   fun scdk (lCon1, lCon2, 0) = lCon1
	     | scdk (I.Decl (lCon1, lc as (LaxCon, _)),
		     I.Decl (lCon2,       (LaxCon, _)), lx) =
		I.Decl (scdk (lCon1, lCon2, lx-1), lc)
	     | scdk (I.Decl (lCon1, (LaxCon, cid)),
		     I.Decl (lCon2, (UsedCon,  _)), lx) =
		I.Decl (scdk (lCon1, lCon2, lx-1), (StrictCon, cid))
	     | scdk (I.Decl (lCon1, lc), I.Decl (lCon2, _), lx) =
		I.Decl (scdk (lCon1, lCon2, lx), lc)
	 in
	   (scdk (lCon1, lCon2, lx1), st1 + lx1 - lx2, lx2)
	 end

    (* makeLax (dProg) => dProg'
       Invariants:
         If    dProg = (G,dPool,st,lx)
         then  dProg' = (G,dPool',0,st+lx)
         and for i=1..|dPool|,
	   - dPool'_i = Lax r    if dPool_i  = Strict r
           - dPool'_i = dPool_i  otherwise
    *)
    fun makeLax (dProg as (G, dPool, 0, lx)) = dProg
      | makeLax (G, dPool, st, lx) =
         let
	   fun makeLax' (dPool', 0) = dPool'
	     | makeLax' (I.Decl (dPool', Strict r), st) =
		I.Decl (makeLax' (dPool', st-1), Lax r)
	     | makeLax' (I.Decl (dPool', cl), st) =
	        I.Decl (makeLax' (dPool', st), cl)
	 in
	   (G, makeLax' (dPool, st), 0, lx+st)
	 end

    (* makeConLax LC => LC'
       Invariants:
         If    LC = (lCon,st,lx)
         then  LC' = (lCon',st',lx')
         and   |lCon| = |lCon'|
         and for i=1..|lCon|,
	   - lCon'_i = (LaxCon, cid)    if lCon_i  = (StrictCon, cid)
           - lCon'_i = lCon_i           otherwise
    *)
    fun makeConLax (LC as (lCon, 0, lx)) = LC
      | makeConLax (lCon, st, lx) =
         let
	   fun makeConLax' (lCon', 0) = lCon'
	     | makeConLax' (I.Decl (lCon', (StrictCon, cid)), st) =
		I.Decl (makeConLax' (lCon', st-1), (LaxCon, cid))
	     | makeConLax' (I.Decl (lCon', lc), st) =
		I.Decl (makeConLax' (lCon', st), lc)
	 in
	   (makeConLax' (lCon, st), 0, lx+st)
	 end

    (* restoreStrict (dProg1,dProg2) => dProg'
       Invariants:
         If    dProg1 = (G, dPool1, st, lx1)
         and   dProg2 = (G, dPool2,  0, lx2)
         and   for i=1..|dPool1|,
	        - if dPool1_i = Strict r, then dPool2_i = Lax r or Used r
	        - if dPool1_i = Lax r,    then dPool2_i = Lax r or Used r
	        - dPool1_i = dPool2_i     otherwise
         then  dProg' = (G, dPool', st', lx')
         and for i=1..|dPool1|,
           - dPool'_i = Strict r  if dPool1_i = Strict r and dPool2_i = Lax _
	   - dPool'_i = Lax r     if dPool1_i = Lax r and dPool2_i = Lax _
           - dPool'_i = dPool2_i  otherwise
    *)
    fun restoreStrict (dProg1, dProg2 as (G2, dPool2, _, 0)) = dProg2
      | restoreStrict (dProg1 as (G, dPool1, 0, lx1), dProg2) = dProg2
      | restoreStrict ((G, dPool1, st1, lx1), (_, dPool2, _, lx2)) =
         let
	   fun rs (dPool1, dPool2, 0) = (dPool2, 0, 0)
	     | rs (I.Decl(dPool1, cl as Strict _), I.Decl(dPool2, Lax _), n) =
		let val (dPool', st', lx') = rs (dPool1, dPool2, n-1)
		in (I.Decl (dPool', cl), st'+1, lx') end
	     | rs (I.Decl(dPool1,Strict _), I.Decl(dPool2, cl as Used _), n) =
		let val (dPool', st', lx') = rs (dPool1, dPool2, n-1)
		in (I.Decl (dPool', cl), st', lx') end
	     | rs (I.Decl (dPool1, Lax _), I.Decl (dPool2, cl as Lax _), n) =
		let val (dPool', st', lx') = rs (dPool1, dPool2, n-1)
		in (I.Decl (dPool', cl), st', lx'+1) end
	     | rs (I.Decl (dPool1, Lax _), I.Decl (dPool2, cl as Used _), n) =
		let val (dPool', st', lx') = rs (dPool1, dPool2, n-1)
		in (I.Decl (dPool', cl), st', lx') end
	     | rs (I.Decl (dPool1, _), I.Decl (dPool2, cl), n) =
		let val (dPool', st', lx') = rs (dPool1, dPool2, n)
		in (I.Decl (dPool', cl), st', lx') end
	   val (dPool, st, lx) = rs (dPool1, dPool2, st1 + lx1)
	 in
	   (G, dPool, st, lx)
	 end

    (* restoreStrictCon (LC1, LC2) => LC'
       Invariants:
         If    LC1 = (lCon1, st, lx1)
         and   LC2 = (lCon2, 0, lx2)
         and   |lCon1| = |lCon2|
         and   for i=1..|lCon1|,
	        - if lCon1_i = (StrictCon, cid), then lCon2_i = (LaxCon, cid)
                                                             or (UsedCon, cid)
	        - if lCon1_i = (LaxCon, cid),    then lCon2_i = (LaxCon, cid)
                                                             or (UsedCon, cid)
	        - lCon1_i = lCon2_i              otherwise
         then  LC' = (lCon', st', lx')
         and   |lCon'| = |lCon1|
         and for i=1..|lCon1|,
           - lCon'_i = (StrictCon, cid)  if  lCon1_i = (StrictCon, cid)
                                         and lCon2_i = (LaxCon, _)
	   - lCon'_i = (LaxCon, cid)     if  lCon1_i = (LaxCon, cid)
                                         and lCon2_i = (LaxCon, _)
           - lCon'_i = lCon2_i           otherwise
    *)
    fun restoreStrictCon (LC1, LC2 as (lCon2, _, 0)) = LC2
      | restoreStrictCon (LC1 as (lCon1, 0, lx1), LC2) = LC2
      | restoreStrictCon ((lCon1, st1, lx1), (lCon2, _, lx2)) =
         let
	   fun rsc (lCon1, lCon2, 0) = (lCon2, 0, 0)
	     | rsc (I.Decl (lCon1, lc as (StrictCon, _)),
		    I.Decl (lCon2,       (LaxCon,    _)), n) =
		let val (lCon', st', lx') = rsc (lCon1, lCon2, n-1)
		in (I.Decl (lCon', lc), st'+1, lx') end
	     | rsc (I.Decl (lCon1,       (StrictCon, _)),
		    I.Decl (lCon2, lc as (UsedCon,   _)), n) =
		let val (lCon', st', lx') = rsc (lCon1, lCon2, n-1)
		in (I.Decl (lCon', lc), st', lx') end
	     | rsc (I.Decl (lCon1,       (LaxCon, _)),
		    I.Decl (lCon2, lc as (LaxCon, _)), n) =
		let val (lCon', st', lx') = rsc (lCon1, lCon2, n-1)
		in (I.Decl (lCon', lc), st', lx'+1) end
	     | rsc (I.Decl (lCon1,       (LaxCon, _)),
		    I.Decl (lCon2, lc as (UsedCon, _)), n) =
		let val (lCon', st', lx') = rsc (lCon1, lCon2, n-1)
		in (I.Decl (lCon', lc), st', lx') end
	     | rsc (I.Decl (lCon1, _), I.Decl (lCon2, lc), n) =
		let val (lCon', st', lx') = rsc (lCon1, lCon2, n)
		in (I.Decl (lCon', lc), st', lx') end
	 in
	   rsc (lCon1, lCon2, st1 + lx1)
	 end

    (* intersect (dProg1,dProg2) => dProg'
       Invariants:
         If    dProg1 = (G, dPool1, st, lx1)
         and   dProg2 = (G, dPool2,  0, lx2)
         and   for i=1..|dPool1|,
	        - if dPool1_i = Strict r, then dPool2_i = Lax r or Used r
	        - if dPool1_i = Lax r,    then dPool2_i = Lax r or Used r
	        - dPool1_i = dPool2_i     otherwise
         then  dProg' = (G, dPool', 0, lx')
         and for i=1..|dPool1|,
           - dPool'_i = Used r  if dPool1_i = Strict r and dPool2_i = Lax _
           - dPool'_i = dPool2_i  otherwise
    *)
    fun intersect ((G, dPool1, 0, lx1), dProg2) = dProg2
      | intersect (dProg1, dProg2 as (G, dPool2, _, 0)) = dProg2
      | intersect ((G, dPool1, st1, lx1), dProg2 as (_, dPool2, _, lx2)) =
         let
	   fun intersect' (dPool1, dPool2, 0, lx) = (dPool2, lx)
	     | intersect' (dPool1, dPool2, st, 0) = (dPool2, 0)
	     | intersect' (I.Decl (dPool1, Strict _),
			   I.Decl (dPool2, Lax r), st, lx) =
		let val (dPool', lx') = intersect' (dPool1, dPool2, st-1, lx-1)
		in (I.Decl (dPool', Used r), lx') end
	     | intersect' (I.Decl (dPool1, Strict _),
			   I.Decl (dPool2, cl), st, lx) =
		let val (dPool', lx') = intersect' (dPool1, dPool2, st-1, lx)
		in (I.Decl (dPool', cl), lx') end
	     | intersect' (I.Decl (dPool1, _),
			   I.Decl (dPool2, cl as Lax _), st, lx) =
		let val (dPool', lx') = intersect' (dPool1, dPool2, st, lx-1)
		in (I.Decl (dPool', cl), lx') end
	     | intersect' (I.Decl (dPool1, _), I.Decl (dPool2, cl), st, lx) = 
		let val (dPool', lx') = intersect' (dPool1, dPool2, st, lx)
		in (I.Decl (dPool', cl), lx') end
	   val (dPool, lx) = intersect' (dPool1, dPool2, st1, lx2)
	 in
	   (G, dPool, 0, lx)
	 end

    (* intersectCon (LC1,LC2) => LC'
       Invariants:
         If    LC1 = (G, lCon1, st, lx1)
         and   LC2 = (G, lCon2,  0, lx2)
         and   for i=1..|lCon1|,
	        - if lCon1_i = (StrictCon, cid), then lCon2_i = (LaxCon, cid)
	                                                     or (UsedCon, cid)
	        - if lCon1_i = (LaxCon, cid),    then lCon2_i = (LaxCon, cid)
							     or (UsedCon, cid)
	        - lCon1_i = lCon2_i              otherwise
         then  LC' = (G, lCon', 0, lx')
         and for i=1..|lCon1|,
           - lCon'_i = (UsedCon, cid)  if  lCon1_i = (StrictCon, cid)
                                       and lCon2_i = (LaxCon, _)
           - lCon'_i = lCon2_i         otherwise
    *)
    fun intersectCon ((lCon1, 0, lx1), dProg2) = dProg2
      | intersectCon (LC1, LC2 as (lCon2, _, 0)) = LC2
      | intersectCon ((lCon1, st1, lx1), LC2 as (lCon2, _, lx2)) =
         let
	   fun intersectCon' (lCon1, lCon2, 0, lx) = (lCon2, lx)
	     | intersectCon' (lCon1, lCon2, st, 0) = (lCon2, 0)
	     | intersectCon' (I.Decl (lCon1, (StrictCon, _)),
			      I.Decl (lCon2, (LaxCon,  cid)), st, lx) =
		let val (lCon', lx') = intersectCon' (lCon1, lCon2, st-1, lx-1)
		in (I.Decl (lCon', (UsedCon, cid)), lx') end
	     | intersectCon' (I.Decl (lCon1, (StrictCon, _)),
			      I.Decl (lCon2, lc), st, lx) =
		let val (lCon', lx') = intersectCon' (lCon1, lCon2, st-1, lx)
		in (I.Decl (lCon', lc), lx') end
	     | intersectCon' (I.Decl (lCon1, _),
			      I.Decl (lCon2, lc as (LaxCon, _)), st, lx) =
		let val (lCon', lx') = intersectCon' (lCon1, lCon2, st, lx-1)
		in (I.Decl (lCon', lc), lx') end
	     | intersectCon' (I.Decl (lCon1, _), I.Decl (lCon2, lc), st, lx) = 
		let val (lCon', lx') = intersectCon' (lCon1, lCon2, st, lx)
		in (I.Decl (lCon', lc), lx') end
	   val (lCon, lx) = intersectCon' (lCon1, lCon2, st1, lx2)
	 in
	   (lCon, 0, lx)
	 end

    (* eraseLinear (dProg) => dProg'
       Invariants:
         If    dProg = (G,dPool,st,lx)
         then  dProg' = (G,dPool',0,)
         and for i=1..|dPool|,
	   - dPool'_i = Used r   if dPool_i = Strict r or Used r
           - dPool'_i = dPool_i  otherwise
    *)
    fun eraseLinear (dProg as (G, dPool, 0, 0)) = dProg
      | eraseLinear (G, dPool, st, lx) = 
         let
	   fun eraseLinear' (dPool, 0) = dPool
	     | eraseLinear' (I.Decl (dPool, Strict r), n) =
		I.Decl (eraseLinear' (dPool, n-1), Used r)
	     | eraseLinear' (I.Decl (dPool, Lax r), n) =
		I.Decl (eraseLinear' (dPool, n-1), Used r)
	     | eraseLinear' (I.Decl (dPool, cl), n) =
		I.Decl (eraseLinear' (dPool, n), cl)
	 in
	   (G, eraseLinear' (dPool, st+lx), 0, 0)
	 end

    (* eraseLinearCon (LC) => LC'
       Invariants:
         If    LC = (lCon,st,lx)
         then  LC' = (lCon',0,)
         and   |lCon| = |lCon'|
         and for i=1..|lCon|,
	   - lCon'_i = (UsedCon, cid)   if lCon_i = (StrictCon, cid)
	                                         or (LaxCon, cid)
           - lCon'_i = lCon_i           otherwise
    *)
    fun eraseLinearCon (LC as (lCon, 0, 0)) = LC
      | eraseLinearCon (lCon, st, lx) = 
         let
	   fun eraseLinearCon' (lCon, 0) = lCon
	     | eraseLinearCon' (I.Decl (lCon, (StrictCon, cid)), n) =
		I.Decl (eraseLinearCon' (lCon, n-1), (UsedCon, cid))
	     | eraseLinearCon' (I.Decl (lCon, (LaxCon, cid)), n) =
		 I.Decl (eraseLinearCon' (lCon, n-1), (UsedCon, cid))
	     | eraseLinearCon' (I.Decl (lCon, lc), n) =
		 I.Decl (eraseLinearCon' (lCon, n), lc)
	 in
	   (eraseLinearCon' (lCon, st+lx), 0, 0)
	 end

  (* solve' ((g,s), dProg, LC, sc) => ()
     Invariants:
       dProg = (G,dPool,st,lx)
       LC = (lCon,st',lx')
       G |- s : G'
       G' |- g :: goal
       if  G \ Go |-sl M :: g[s],
        then G |- sc :: (Go,sl,g[s]) => Answer, Answer closed
  *)
  fun solve' ((Atom(p), s), dProg, LC, sc) = matchAtom' ((p,s), dProg, LC, sc)
    | solve' ((ATruth, s), dProg, LC, sc) =
       sc (eraseStrict(dProg), eraseStrictCon(LC), Slack, I.Unit)
    | solve' ((AConj(g1, g2), s), dProg, LC, sc) =
       solve' ((g1, s), dProg, LC,
	      fn (midDProg, midLC, NoSlack, U1) =>
	          solve' ((g2, s), strictDiff_erase (dProg, midDProg),
			           strictConDiff_erase (LC, midLC),
			 fn (_, _, _, U2) =>
			     sc (midDProg, midLC, NoSlack, I.Pair (U1, U2)))
	       | (midDProg, midLC, Slack, U1) =>
		  solve' ((g2, s), strictDiff_keep (dProg, midDProg),
			           strictConDiff_keep (LC, midLC),
			 fn (newDProg, newLC, sl, U2) =>
			     sc (newDProg, newLC, sl, I.Pair (U1, U2))))
    | solve' ((Lolli(r, A, cid, g), s), (G,dPool,st,lx), LC, sc) =
       let
	 val D' = I.LDec(NONE, I.EClo(A,s))
	 val dProg' = (I.Decl (G, D'),
		       I.Decl (dPool, Strict (r, s, cid)),
		       st+1, lx)
       in
	 solve' ((g, I.ldot1 s), dProg', LC,
		(fn ((_, I.Decl(dPool',Used _), st', lx'), LC', sl, U) =>
		     sc ((G,dPool',st',lx'), LC', sl, I.Lam (D', U))))
       end
    | solve' ((Impl(r, A, cid, g), s), (G,dPool,st,lx), LC, sc) =
       let
	 val D' = I.Dec(NONE, I.EClo(A,s))
	 val dProg' = (I.Decl (G, D'),
		       I.Decl (dPool, Reusable (r, s, cid)),
		       st, lx)
       in
	 solve' ((g, I.dot1 s), dProg', LC,
		(fn ((_, I.Decl (dPool',_), st', lx'), LC', sl, U) =>
		      sc ((G,dPool',st',lx'), LC', sl, I.Lam (D', U))))
       end
    | solve' ((All(D, g), s), (G,dPool,st,lx), LC, sc) =
       let
	 val D' = I.decSub (D, s)
	 val dProg' = (I.Decl(G, D'), I.Decl(dPool, Param), st, lx)
       in
	 solve' ((g, I.dot1 s), dProg', LC,
		(fn ((_, I.Decl (dPool',_), st', lx'), LC', sl, U) =>
		      sc ((G,dPool',st',lx'), LC', sl, I.Lam (D', U))))
       end

  (* rsolve' ((p,s'), (r,s), dProg, LC, sc) = ()
     Invariants:
       dProg = (G,dPool,st,lx)
       LC = (lCon,st',lx')
       G |- s : G'
       G' |- r :: resgoal
       G |- s' : G''
       G'' |- p :: atom
       if G \ Go |-sl S :: r[s] then G |- sc : (Go, sl, r >> p[s']) => Answer
  *)
  and rSolve' (ps', (Eq(Q), s), dProg as (G,dPool,0,lx), LC, sc) =
      ((Unify.unify (ps', (Q, s)); sc (dProg, LC, NoSlack, I.Nil))
       handle Unify.Unify _ => ())
    | rSolve' (ps', (Eq _, s), (G,dPool,_,lx), LC, sc) = ()
    | rSolve' (ps', (Plus (r1, r2), s), dProg, LC, sc) =
       (Trail.trail (fn () =>
                    (rSolve' (ps', (r1, s), dProg, LC,
                              fn (newDProg, newLC, sl, S) =>
			        sc (newDProg, newLC, sl, I.Pi1 S)))) ;
        rSolve' (ps', (r2, s), dProg, LC,
                 fn (newDProg, newLC, sl, S) =>
		   sc (newDProg, newLC, sl, I.Pi2 S)))
    | rSolve' (ps', (Tensor (r, A, g), s), dProg, LC, sc) =
      let
	val X = I.newEVar (I.EClo(A, s))
      in
        rSolve' (ps', (r, I.LDot(I.Exp(X,A),s)),
		 makeLax dProg, makeConLax LC,
		(fn (midDProg, midLC, NoSlack, S) =>
		     solve' ((g, s), restoreStrict (dProg, midDProg),
			             restoreStrictCon (LC, midLC),
			    (fn (newDProg, newLC, sl, U) =>
			         sc (newDProg, newLC, sl, (I.LApp (U, S)))))
		  | (midDProg, midLC, Slack, S) =>
		     solve' ((g, s), midDProg, midLC,
			    (fn (newDProg, newLC, _, U) =>
			         sc (intersect (dProg, newDProg),
				     intersectCon (LC, newLC),
				     Slack, I.LApp (U, S))))))
      end
    | rSolve' (ps', (And(r, A, g), s), dProg, LC, sc) =
      let
	val X = I.newEVar (I.EClo(A, s))
      in
        rSolve' (ps', (r, I.Dot(I.Exp(X,A),s)), dProg, LC,
		(fn (midDProg, midLC, sl, S) =>
		     solve' ((g, s), eraseLinear dProg, eraseLinearCon LC,
			    (fn (_, _, _, U) =>
			         sc (midDProg, midLC, sl, I.App (U, S))))))
      end
    | rSolve' (ps', (Exists(I.Dec(_,A),r), s), dProg, LC, sc) =
      let
	val X = I.newEVar (I.EClo (A,s))
      in
	rSolve' (ps', (r, I.Dot(I.Exp(X,A), s)), dProg, LC,
		(fn (newDProg, newLC, sl, S) =>
		   sc (newDProg, newLC, sl, I.App(X,S))))
       end

  (* matchatom ((p, s), dProg, LC, sc) => ()
     Invariants:
       dProg = (G,dPool,st,lx)
       LC = (lCon,st',lx')
       G |- s : G'
       G' |- p :: atom
       if G \ Go |-sl M :: p[s] then G |- sc :: (Go, sl, p[s]) => Answer
  *)
  and matchAtom' (ps' as (I.Root(I.Const(cid),_),_),
		 dProg as (G,dPool,st,lx),
		 LC as (lCon,st',lx'), sc) =
      let
	fun matchSig () =
	  let
	    fun matchSig' (Index.Empty, _, _) = ()
	      | matchSig' (Index.Entry(cid',sgn'), LCP, lCon as I.Null) =
	         let
		   val SClause(r) = sProgLookup cid'
		 in
		   Trail.trail (fn () =>
				rSolve' (ps', (r, I.id), dProg, LC,
					 (fn (newDProg, newLC, sl, S) =>
					   sc (newDProg, newLC, sl,
					       I.Root(I.Const(cid'),S)))));
		   matchSig' (sgn', LCP, lCon)
		 end
	      | matchSig' (sgn as Index.Entry(cid',sgn'), LCP,
			   lCon as I.Decl (lCon', lc as (tag,lcid))) =
		 let
		   val SClause(r) = sProgLookup cid'
		 in
		   (case (tag, Int.compare (lcid, cid'))
		      of (_, GREATER) =>
			 (Trail.trail (fn () =>
				       rSolve' (ps', (r, I.id), dProg, LC,
						(fn (newDProg, newLC, sl, S) =>
						  sc (newDProg, newLC, sl,
						      I.Root(I.Const(cid'),S)))));
			  matchSig' (sgn', LCP, lCon))

		       | (_, LESS) =>
			  matchSig' (sgn, (fn K => LCP (I.Decl (K, lc))), lCon')

		       | (UsedCon, EQUAL) =>
			 matchSig' (sgn', (fn K => LCP (I.Decl (K, lc))), lCon')

		       | (StrictCon, EQUAL) =>
			 (Trail.trail (fn () =>
				       rSolve' (ps', (r, I.id), dProg,
						(LCP (I.Decl (lCon', (UsedCon, lcid))), st'-1, lx'),
						(fn (newDProg, newLC, sl, S) =>
						  sc (newDProg, newLC, sl,
						      I.Root(I.Const(cid'),S)))));
			  matchSig' (sgn', (fn K => LCP (I.Decl (K, lc))), lCon'))

		       | (LaxCon, EQUAL) =>
			 (Trail.trail (fn () =>
				       rSolve' (ps', (r, I.id), dProg,
						(LCP (I.Decl (lCon', (UsedCon, lcid))), st', lx'-1),
						(fn (newDProg, newLC, sl, S) =>
						  sc (newDProg, newLC, sl,
						      I.Root(I.Const(cid'),S)))));
			  matchSig' (sgn', (fn K => LCP (I.Decl (K, lc))), lCon')))
		 end
	  in
	    matchSig' (Index.lookup cid, fn lCon' => lCon', lCon)
	  end
(*
	fun matchSig () =
	    let
	      fun matchSig' (Index.Empty) = ()
		| matchSig' (Index.Entry(cid',sgn')) =
		  let
		    val SClause(r) = sProgLookup cid'
		  in
		    Trail.trail (fn () =>
				 rSolve' (ps', (r, I.id), dProg,
					 (fn (newDProg, sl, S) =>
					       sc (newDProg, sl,
						   I.Root(I.Const(cid'),S)))));
		    matchSig' sgn'
		  end
	    in
	      matchSig' (Index.lookup cid)
	    end
*)
	fun matchDProg (_, I.Null, _) = matchSig ()
	  | matchDProg (dpStart, I.Decl (dPool',cl as Reusable(r,s,cid')), k) =
	    if cid = cid' then
	      (Trail.trail (fn () =>
			    rSolve' (ps', (r, I.comp(s, I.Shift(k))), dProg, LC,
				    (fn (newDProg, newLC, sl, S) =>
				          sc (newDProg, newLC, sl,
					      I.Root(I.BVar(k), S))))) ;
	       matchDProg (fn rest => dpStart (I.Decl (rest, cl)),
			   dPool', k+1))
	    else matchDProg (fn rest => dpStart (I.Decl (rest, cl)),
			     dPool', k+1)
	  | matchDProg (dpStart,
			I.Decl (dPool', cl as Strict (res as (r,s,cid'))),
			k) =
	    if cid = cid' then
	      (Trail.trail (fn () =>
			    rSolve' (ps', (r, I.comp(s, I.Shift(k))),
				    (G, dpStart (I.Decl (dPool', Used res)),
				     st-1, lx), LC,
				    (fn (newDProg, newLC, sl, S) =>
				          sc (newDProg, newLC, sl,
					      I.Root(I.BVar(k), S))))) ;
	       matchDProg (fn rest => dpStart (I.Decl (rest, cl)),
			   dPool', k+1))
	    else matchDProg (fn rest => dpStart (I.Decl (rest, cl)),
			     dPool', k+1)
	  | matchDProg (dpStart,
			I.Decl (dPool', cl as Lax (res as (r,s,cid'))),
			k) =
	    if cid = cid' then
	      (Trail.trail (fn () =>
			    rSolve' (ps', (r, I.comp(s, I.Shift(k))),
				    (G, dpStart (I.Decl (dPool', Used res)),
				     st, lx-1), LC,
				    (fn (newDProg, newLC, sl, S) =>
				          sc (newDProg, newLC, sl,
					      I.Root(I.BVar(k), S))))) ;
	       matchDProg (fn rest => dpStart (I.Decl (rest, cl)),
			   dPool', k+1))
	    else matchDProg (fn rest => dpStart (I.Decl (rest, cl)),
			     dPool', k+1)
	  | matchDProg (dpStart, I.Decl (dPool', cl), k) =
	       matchDProg (fn rest => dpStart (I.Decl (rest, cl)),
			   dPool', k+1)	      
      in
	matchDProg (fn x => x, dPool, 1)
      end

  end (* local ... *)

  fun solve (gs, dProg, sc) =
       let
	 fun sc' (dProg, LC, Slack, U) = sc U
	   | sc' ((G, dPool, 0, 0), LC as (lCon, 0, 0), NoSlack, U) =
	      sc U
	   | sc' _ = ()
       in
	 solve' (gs, dProg, !CompSyn.linCon, sc')
       end

  fun rSolve (gs', gs, dProg, sc) =
	 rSolve' (gs', gs, dProg, !CompSyn.linCon, fn (_, _, _, S) => sc S)

  fun matchAtom (gs', dProg, sc) =
	 matchAtom' (gs', dProg, !CompSyn.linCon, fn (_, _, _, U) => sc U)

end; (* functor AbsMachine *)
