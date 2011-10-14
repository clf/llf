(* Paths, Occurrences, and Error Locations *)
(* Author: Frank Pfenning *)

functor Paths () :> PATHS =
struct

  type pos = int			(* characters, starting at 0 *)
  type region = pos * pos		(* (i,j) is interval [i,j) *)
  type location = string * region	(* filename, character region *)

  local
    val linePosList = ref nil : pos list ref
  in
    fun resetLines () = linePosList := nil
    fun newLine (i) = linePosList := i::(!linePosList)
    fun posToLineCol (i) =
        let fun ptlc (j::js) = if i >= j then (List.length js, i-j)
			       else ptlc js
	    (* first line should start at 0---nil should not happen *)
	in
	  ptlc (!linePosList)
	end
  end
	  

  (* val join : region * region -> region *)
  fun join ((i1, j1), (i2, j2)) = (Int.min (i1, i2), Int.max (j1, j2))

  (* The right endpoint of the interval counts IN RANGE *)
  fun posInRegion (k:pos, (i,j):region) = i <= k andalso k <= j

  fun lineColToString (line,col) =
      Int.toString (line+1) ^ "." ^ Int.toString (col+1)

  (* val toString : region -> string *)
  (* fun toString (i,j) = Int.toString (i+1) ^ "-" ^ Int.toString (j+1) *)
  fun toString (i,j) = lineColToString (posToLineCol i) ^ "-"
                       ^ lineColToString (posToLineCol j)

  (* maintain occurrences when traversing a term *)
  (* match paths when locating a subterm *)
  (* applies only to normal forms---recognize if mismatch *)
  (*
     We generally assume an occurrence or path matches an occurrence
     matches an occurrence expressions
  *)

  datatype Path =
     Label of Path			(* [x:#]U, [x^#]U, {x:#}V or {x^#}V *)
   | Body of Path			(* [x:V]#, [x^V]#, {x:V}# or {x^V}# *)
   | Pair1 of Path                      (* (#, U'') or # & V'' *)
   | Pair2 of Path			(* (U', #)  or V' & # *)
   | Head				(* # @ S, term in normal form *)
   | Arg of int * Path			(* C @ S1; ...; #; ...; Sn; Nil *)
   | Here				(* #, covers Uni, Top, Unit, EVar, Redex(?) *)

  (* Occurrences: paths in reverse order *)
  (* could also be: type occ = path -> path *)
  datatype occ =
      top
    | label of occ
    | body of occ
    | pair1 of occ
    | pair2 of occ
    | head of occ
    | arg of int * occ

  (* Occurrence expressions and spines *)
  (* Maps between regions and paths/occurrences *)
  (* Simple-minded implementation *)
  datatype occExp =
      leaf of region			(* _ or identifier *)
    | bind of region * occExp option * occExp
    | pair of region * occExp * occExp
    | root of region * occExp * int * occSpine (* implicit args *)
  and occSpine =
      app of occExp * occSpine
    | proj of occSpine
    | nils

  fun occToPath (top, path) = path
    | occToPath (label(occ), path) = occToPath (occ, Label(path))
    | occToPath (pair1(occ), path) = occToPath (occ, Pair1(path))
    | occToPath (pair2(occ), path) = occToPath (occ, Pair2(path))
    | occToPath (body(occ), path) = occToPath (occ, Body(path))
    | occToPath (head(occ), path) =
      (* path = Here by invariant *)
        occToPath (occ, Head)
    | occToPath (arg(n,occ), path) = occToPath (occ, Arg(n,path))

  datatype occEntry =
      decl of region * int * occExp	(* implicit abstractions *)
    | defn of region * int * occExp * occExp option

  (* val posToPath : occExp -> pos -> Path *)
  (* Path might be optional or marked if addressed subterm is implicit *)
  (* This returns a path to the innermost expression for co-terminating *)
  (* terms *)
  fun posToPath u k =
      let
	  fun inside (leaf r) = posInRegion (k, r)
	    | inside (bind (r, _, _)) = posInRegion (k, r)
	    | inside (pair (r, _, _)) = posInRegion (k, r)
	    | inside (root (r, _, _, _)) = posInRegion (k, r)

	  fun toPath (leaf (i,j)) = Here (* check? mark? *)
	    | toPath (bind ((i,j), NONE, u)) =
              if inside u then Body (toPath u)
	      else Here
	    | toPath (bind ((i,j), SOME(u1), u2)) =
	      if inside u1 then Label (toPath u1)
	      else if inside u2 then Body (toPath u2)
		   else Here
	    | toPath (pair ((i,j), u1, u2)) =
	       if inside u1
		 then Pair1 (toPath u1)
	       else if inside u2
		 then Pair2 (toPath u2)
		    else Here
	    | toPath (root ((i,j), h, imp, s)) =
	      if inside h then Head
	      else (case toPathSpine (s, 1)
		      of NONE => Here
		       | SOME(n, path) => Arg (n+imp, path))
	  (* in some situations, whitespace after subexpressions *)
          (* might give a larger term than anticipated *)
	  and toPathSpine (nils, n) = NONE
	    | toPathSpine (app(u,s), n) =
	      if inside u then SOME(n, toPath u)
	      else toPathSpine (s, n+1)
	    | toPathSpine (proj s, n) = toPathSpine (s, n)
		(* if error in subsequent application, will point there,
		   othewise to the whole root *)
      in
	toPath u
      end

  fun toRegion (leaf r) = r
    | toRegion (bind (r, _, _)) = r
    | toRegion (pair (r, _, _)) = r
    | toRegion (root (r, _, _, _)) = r

  fun toRegionSpine (nils, r) = r
    | toRegionSpine (app (u, s), r) =
        join (toRegion u, toRegionSpine (s, r))
    | toRegionSpine (proj s, r) = toRegionSpine (s, r)

  (* future improvement? *)
  (*
  exception Implicit of region
  *)

  fun pathToRegion (u, Here) = toRegion u
    | pathToRegion (pair (r, u1, _), Pair1(path)) =
       pathToRegion (u1, path)
    | pathToRegion (pair (r, _, u2), Pair2(path)) =
       pathToRegion (u2, path)
    | pathToRegion (bind (r, NONE, u), Label(path)) =
      (* strange: addressing implicit type label *)
      (* for now: unaddressable *)
      (* actually: do best job possible *)
      (* raise Implicit(r) *)
      r
    | pathToRegion (bind (r, SOME(u1), u2), Label(path)) =
        pathToRegion (u1, path)
    | pathToRegion (bind (r, _, u), Body(path)) =
	pathToRegion (u, path)
    | pathToRegion (root (r, h, imp, s), Head) = toRegion h
    | pathToRegion (root (r, h, imp, s), Arg (n, path)) =
      if n <= imp
	then (* raise Implicit(r) *) (* or Implicit (toRegion h) ? *)
	     toRegion h
      else pathToRegionSpine (s, n-imp, path)
    (* other combinations should be impossible *)
  and pathToRegionSpine (app (u, s), 1, path) =
        pathToRegion (u, path)
    | pathToRegionSpine (app (u, s), n, path) =
	pathToRegionSpine (s, n-1, path)
    | pathToRegionSpine (proj s, n, path) =
	pathToRegionSpine (s, n, path)
    (* anything else should be impossible *)

  (* val occExpToRegion : occExp -> occ -> region *)
  fun occToRegionExp u occ = pathToRegion (u, occToPath (occ, Here))

  fun skipImplicit (r, 0, path) = path
    | skipImplicit (r, n, Body(path)) =
        skipImplicit (r, n-1, path)
    | skipImplicit (r, n, Label(path)) =
	(* implicit argument: approximate as best possible *)
	(* raise Implicit(r) *)
	Here
    (* anything else should be impossible *)

  (* val occEntryToRegion : occEntry -> occ -> region *)
  fun occToRegionDecl (decl (r, n, u)) occ =
      pathToRegion (u, skipImplicit (r, n, occToPath (occ, Here)))

  fun occToRegionDefn1 (defn (r, n, u, vOpt)) occ =
      pathToRegion (u, skipImplicit (r, n, occToPath (occ, Here)))

  fun occToRegionDefn2 (defn (r, n, u, NONE)) occ = r
    | occToRegionDefn2 (defn (r, n, u, SOME(v))) occ =
      pathToRegion (v, skipImplicit (r, n, occToPath (occ, Here)))

end;  (* functor Paths *)
