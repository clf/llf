(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

signature FIXITY =
sig

  datatype associativity = Left | Right | None

  type precedence = int
  val maxPrec : precedence
  val minPrec : precedence

  val projPrec  : precedence
  val appPrec   : precedence
  val absPrec   : precedence
  val withPrec  : precedence
  val arrowPrec : precedence
  val pairPrec  : precedence
  val colonPrec : precedence
  val piPrec    : precedence
  val ctxPrec   : precedence

  datatype fixity =
      Nonfix
    | Infix of precedence * associativity
    | Prefix of precedence
    | Postfix of precedence

  val prec : fixity -> precedence
  val toString : fixity -> string

end;  (* signature FIXITY *)

signature NAMES =
sig

  structure IntSyn : INTSYN

  exception Error of string

  structure Fixity : FIXITY

  (* Constant names and fixities *)
  val reset : unit -> unit

  val installFixity : string * Fixity.fixity -> unit
  val getFixity : IntSyn.cid -> Fixity.fixity
  val fixityLookup : IntSyn.name -> Fixity.fixity

  val installName : IntSyn.name * IntSyn.cid -> unit
  val nameLookup : IntSyn.name -> IntSyn.cid option
  val constName : IntSyn.cid -> string	(* will mark if shadowed *)

  (* Name preferences for anonymous variables *)
  val installNamePref : IntSyn.name * IntSyn.name -> unit

  (* EVar and BVar name choices *)
  val varReset : unit -> unit
  val getFVarType : IntSyn.name -> IntSyn.Exp (* create, if undefined *)
  val getEVar : IntSyn.name -> IntSyn.Exp (* create, if undefined *)
  val evarName : IntSyn.dctx * IntSyn.Exp -> string
  val bvarName : IntSyn.dctx * int -> string
  val decName  : IntSyn.dctx * IntSyn.Dec -> IntSyn.Dec

  (* Names EVars, used for queries *)
  val namedEVars : unit -> (IntSyn.Exp * IntSyn.name) list
  (* Uninstantiated named EVars with constraints *)
  val evarCnstr : unit -> string list
end;  (* signature NAMES *)
