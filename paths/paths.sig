(* Paths, Occurrences, and Error Locations *)
(* Author: Frank Pfenning *)

signature PATHS =
sig

  type pos = int			(* characters, starting at 0 *)
  type region = pos * pos		(* (i,j) is interval [i,j) *)
  type location = string * region	(* filename, character region *)

  (* line numbering, used when printing regions *)
  val resetLines : unit -> unit		(* reset line numbering *)
  val newLine : pos -> unit		(* new line starts at i *)

  val join : region * region -> region
  val toString : region -> string

  (* maintain occurrences when traversing a term *)
  (* match paths when locating a subterm *)
  (* applies only to normal forms---recognize if mismatch *)
  (* graceful recovery? *)

  datatype Path =
     Label of Path			(* [x:#]U, [x^#]U, {x:#}V or {x^#}V *)
   | Body of Path			(* [x:V]#, [x^V]#, {x:V}# or {x^V}# *)
   | Pair1 of Path                      (* (#, U'') or # & V'' *)
   | Pair2 of Path			(* (U', #)  or V' & # *)
   | Head				(* # @ S, term in normal form *)
   | Arg of int * Path			(* C @ S1; ...; #; ...; Sn; Nil *)
   | Here				(* #, covers Uni, Top, Unit, EVar, Redex(?) *)

  type occ
  (* implemented as a datatype, this is a path in reverse order *)
  (* could also be: type occ = path -> path *)
  val top : occ
  val label : occ -> occ
  val body : occ -> occ
  val pair1 : occ -> occ
  val pair2 : occ -> occ
  val head : occ -> occ
  val arg : int * occ -> occ

  type occExp
  and occSpine
  (* add variable binding information? *)
  val leaf : region -> occExp		(* could be _ or identifier *)
  val bind : region * occExp option * occExp -> occExp
  val pair : region * occExp * occExp -> occExp
  val root : region * occExp * int * occSpine -> occExp
  val app : occExp * occSpine -> occSpine
  val proj : occSpine -> occSpine
  val nils : occSpine

  type occEntry
  val decl : region * int * occExp -> occEntry
      (* number of implicit abstractions *)
  val defn : region * int * occExp * occExp option -> occEntry


  val toRegion : occExp -> region
  val toRegionSpine : occSpine * region -> region

  (* Path might be optional or marked if addressed subterm is implicit *)
  val posToPath : occExp -> pos -> Path
  val occToRegionExp : occExp -> occ -> region
  val occToRegionDecl : occEntry -> occ -> region
  val occToRegionDefn1 : occEntry -> occ -> region (* into defined expression *)
  val occToRegionDefn2 : occEntry -> occ -> region (* into type or kind *)

end;  (* signature PATHS *)
