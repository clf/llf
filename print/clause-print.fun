(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor ClausePrint
  (structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Formatter' : FORMATTER
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn'
     sharing Print.Formatter = Formatter')
     : CLAUSE_PRINT
  (* :> CLAUSE_PRINT
        where IntSyn = IntSyn'
        where Formatter = Formatter'
  *) =
struct

structure IntSyn = IntSyn'
structure Formatter = Formatter'

local
  (* some shorthands *)
  structure I = IntSyn
  structure F = Formatter
  val Str = F.String

  (* parens for ({x:A} B), (A -> B), or (A -o B) only *)
  (* arg must be in whnf *)
  fun parens (G, Vs as (I.Pi _, s)) =
       F.Hbox [Str "(", Print.formatExp (G, I.EClo Vs), Str ")"]
    | parens (G, Vs) = Print.formatExp (G, I.EClo Vs)

  fun fmtClause (G, (V,s), acc) = fmtClauseW (G, Whnf.whnf (V,s), acc)

  and fmtClauseW (G, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), acc) =
        fmtClause (I.Decl (G, D), (* I.decSub (D, s) *)
		   (V2, I.dot1 s),
		   F.Break
		   :: Str "<-" :: F.Space :: parens (G, Whnf.whnf (V1,s))
		   :: acc)
    | fmtClauseW (G, (I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), s), nil) =
      let
	val D' = Names.decName (G, D)
      in
	Str "{" :: Print.formatDec (G, D') :: Str "}" :: F.Break
	:: fmtClause (I.Decl (G, D'),  (* I.decSub (D', s) *)
		      (V2, I.dot1 s),
		      nil)
      end
    | fmtClauseW (G, (I.Pi ((D as I.LDec (_, V1), _), V2), s), acc) = (* P=No *)
        fmtClause (I.Decl (G, D), (* I.decSub (D, s) *)
		   (V2, I.ldot1 s),
		   F.Break
		   :: Str "o-" :: F.Space :: parens (G, Whnf.whnf (V1,s))
		   :: acc)
    | fmtClauseW (G, (V, s), acc) =
      Print.formatExp (G, I.EClo (V, s)) :: acc

  (*
  fun fmtEntry (I.ConstDec (name, _, V, L)) =
      F.Hbox [Str(name), F.Space, Str ":", F.Break,
	      fmtExp I.Null 0 noCtxt (V, I.id), Str "."]
    | fmtEntry (I.ConstDef (name, _, U, V, L)) =
      (* print the type of definitions? *)
      (* should coordinate variable names between type and definition *)
      F.HVbox [Str(name), F.Space, Str ":", F.Break,
	       fmtExp I.Null 0 noCtxt (V, I.id), F.Break,
	       Str "=", F.Space,
	       fmtExp I.Null 0 noCtxt (U, I.id), Str "."]
    | fmtEntry (I.LinDec (name, _, V, L)) =
      F.Hbox [Str(name), F.Space, Str "^", F.Break,
	      fmtExp I.Null 0 noCtxt (V, I.id), Str "."]
  *)

in

  fun formatClause (G, V) = F.Vbox (fmtClause (G, (V, I.id), nil))
  (* fun formatEntry (e) = fmtEntry (e) *)

  fun clauseToString (G, V) = F.makestring_fmt (formatClause (G, V))
  (*
  fun entryToString (e) =
      ((* Names.varReset (); *)
       F.makestring_fmt (formatEntry (e)))
  *)

end  (* local ... *)

end  (* functor ClausePrint *)
