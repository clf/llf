(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor ModePrint (structure IntSyn' : INTSYN
                     structure Modes' : MODES
		       sharing Modes'.IntSyn = IntSyn'
		     structure Names : NAMES
		       sharing Names.IntSyn = IntSyn'
		     structure Formatter : FORMATTER
		     structure Print : PRINT
		       sharing Print.IntSyn = IntSyn'
		       sharing Print.Formatter = Formatter)
  : MODEPRINT
  (* :> MODEPRINT
        where Modes = Modes'
        where IntSyn = IntSyn'
  *) =
struct
  structure Modes = Modes'
  structure IntSyn = IntSyn' 
    
  local
    structure I = IntSyn
    structure M = Modes
    structure F = Formatter
    structure P = Print
      
    fun modeToString M.PlusPlus = "++"
      | modeToString M.Plus = "+"
      | modeToString M.Star = "*"
      | modeToString M.Minus = "-"
      | modeToString M.MinusMinus = "--"

    fun argToString (M.Marg (m, _)) = modeToString m
    fun nameDec (I.Dec (_, V) , M.Marg (_, name as SOME _)) = I.Dec (name, V)
      | nameDec (D, M.Marg (_, NONE)) = D
      
    fun makeSpine (G) =
      let 
	fun makeSpine' (I.Null, _, S) = S
	  | makeSpine' (I.Decl (G, _), k, S) =  
              makeSpine' (G, k+1, I.App (I.Root (I.BVar k, I.Nil), S))
      in 
	makeSpine' (G, 1, I.Nil)
      end

    fun fmtModeDec (cid, mS) =
      let
	val V = I.constType cid
	fun fmtModeDec' (G, _, M.Mnil) = 
	      [P.formatExp (G, I.Root (I.Const (cid), makeSpine G))]
	  | fmtModeDec' (G, I.Pi ((D, _), V'), M.Mapp (A, S)) =
	      let 
		val D' = nameDec(D, A)
		val D'' = Names.decName (G, D')
	      in
		[F.String ((argToString A) ^ "{"), P.formatDec (G, D''), 
		 F.String "}", F.Break] @ (fmtModeDec' (I.Decl (G, D''), V', S))
	      end
      in
	F.HVbox (fmtModeDec' (I.Null, V, mS))
      end

    fun modeToString cM = F.makestring_fmt (fmtModeDec cM)
  in
    val modeToString = modeToString
  end (* local *)

end; (* functor ModePrint *)
