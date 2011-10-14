(* External Syntax *)
(* Author: Frank Pfenning *)

signature EXTSYN =
sig
  structure Paths : PATHS

  type name = string
  type term
  type decl

  val lcid : string * Paths.region -> term
  val ucid : string * Paths.region -> term
  val quid : string * Paths.region -> term

  val app : term * term -> term
  val linapp : term * term -> term
  val first : term -> term
  val second : term -> term
  val arrow : term * term -> term
  val backarrow : term * term -> term
  val lolli : term * term -> term
  val backlolli : term * term -> term
  val witH : term * term -> term
  val top : Paths.region -> term
  val hastype : term * term -> term
  val omitobj : Paths.region -> term
  val omittyp : Paths.region -> term
  val pi : decl * term * Paths.region -> term
  val lam : decl * term * Paths.region -> term
  val pair : term * term  -> term
  val unit : Paths.region -> term

  val typ : Paths.region -> term

  val decl : name option * term -> decl
  val decl0 : name option -> decl	(* implicit type *)
  val ldecl : name option * term -> decl
  val ldecl0 : name option -> decl	(* implicit type *)

  type sgnentry
  val cdecl : name * term -> sgnentry         (* c : A     or a : K     *)
  val cdefn : name * term * term -> sgnentry  (* c = M : A or a = A : K *)
  val lcdecl : name * term -> sgnentry        (* c ^ A                  *)

end;  (* signature EXTSYN *)

signature TP_RECON =
sig

  structure IntSyn : INTSYN
  include EXTSYN

  val doubleCheck : bool ref

  exception Error of string
  val declToDec : IntSyn.dctx * decl -> IntSyn.Dec
      (* reconstructs x:V such that G |- V : type *)
  val termToExp : IntSyn.dctx * term -> IntSyn.Exp
      (* reconstructs V such that G |- V : type *)
  val termToQuery : term -> IntSyn.Exp * (IntSyn.Exp * IntSyn.name) list

  val entryToEntry : sgnentry * Paths.region ->
                     IntSyn.Entry * Paths.occEntry option

end;  (* signature TP_RECON *)
