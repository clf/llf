(* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann, Iliano Cervesato *)

signature INTSYN =
sig

  type cid = int			(* Constant identifier        *)
  type name = string			(* Variable name              *)

  (* Contexts *)

  datatype 'a Ctx =			(* Contexts                   *)
    Null				(* G ::= .                    *)
  | Decl  of 'a Ctx * 'a       		(*     | G, D                 *)

  val ctxPop : 'a Ctx -> 'a Ctx
  val ctxLookup: 'a Ctx * int -> 'a
  val ctxLength: 'a Ctx -> int

  datatype Depend =                     (* Dependency information     *)
    No                                  (* P ::= No                   *)
  | Maybe                               (*     | Maybe                *)

  (* Expressions *)

  datatype Uni =			(* Universes:                 *)
    Kind				(* L ::= Kind                 *)
  | Type				(*     | Type                 *)

  datatype Exp =			(* Expressions:               *)
    Uni   of Uni			(* U ::= L                    *)
  | Pi    of (Dec * Depend) * Exp	(*     | Pi (D, P). V         *)
                                        (*     | V1 -o V2             *)
  | With  of Exp * Exp			(*     | V1 & V2              *)
  | Top					(*     | T                    *)
  | Root  of Con * Spine		(*     | C @ S                *)
  | Redex of Exp * Spine		(*     | U @ S                *)
  | Lam   of Dec * Exp			(*     | lam D. U             *)
                                        (*     | llam D. U            *)
  | Pair  of Exp * Exp			(*     | <U1, U2>             *)
  | Unit				(*     | <>                   *)
  | EVar  of Exp option ref * Exp * Eqn list
                                        (*     | X<I> : V, Cnstr      *)
  | EClo  of Exp * Sub			(*     | U[s]                 *)

  and Con =				(* Constructors:              *)
    BVar  of int			(* C ::= k                    *)
  | Const of cid			(*     | c                    *)
  | Defn  of cid			(*     | d                    *)
  | FVar  of name * Exp * Sub		(*     | F[s]                 *)
    
  and Spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | App   of Exp * Spine		(*     | U ; S                *)
  | LApp  of Exp * Spine		(*     | U ^ S                *)
  | Pi1   of Spine			(*     | pi1 S                *)
  | Pi2   of Spine			(*     | pi2 S                *)
  | SClo  of Spine * Sub		(*     | S[s]                 *)

  and Sub =				(* Explicit substitutions:    *)
    Shift of int			(* s ::= ^n                   *)
  | Dot   of Head * Sub                 (*     | H.s                  *)
  | LDot  of Head * Sub                 (*     | H^s                  *)

  and Head =				(* Heads:                     *)
    Idx of int				(* H ::= k                    *)
  | Exp of Exp * Exp			(*     | (U:V)                *)

  and Dec =				(* Declarations:              *)
    Dec   of name option * Exp		(* D ::= x:V                  *)
  | LDec  of name option * Exp          (*     | x^V                  *)

  (* Constraint equations *)
    
  and Eqn =				(* Equations                  *)
    Eqn of  Exp * Exp			(* Eqn ::= (U1 == U2)         *)

  type dctx = Dec Ctx			(* G = . | G,D                *)
  type root = Con * Spine               (* R = C @ S                  *)
  type eclo = Exp * Sub   		(* Us = U[s]                  *)

  (* The global LF signature *)
    
  exception Error of string		(* raised if out of space     *)
  
  type imp = int			(* number implicit arguments  *)

  datatype Entry =			(* Signature Entry            *)
    ConstDec of name * imp		(* a : K : kind  or           *)
                * Exp * Uni	        (* c : A : type               *)
  | ConstDef of name * imp		(* a = A : K : kind  or       *)
                * Exp * Exp * Uni	(* d = M : A : type           *)
  | LinDec of name * imp * Exp * Uni    (* c ^ A : type               *)
  (* Linear Constant definition(?)  -ic *)

  val entryName : Entry -> name

  val sgnAdd   : Entry -> cid
  val sgnLookup: cid -> Entry
  val sgnReset : unit -> unit
  val sgnSize  : unit -> int
    
  val constType : cid -> Exp		(* type of Const(c) or Defn(d)*)
  val constDefn : cid -> Exp		(* definition of Defn(d)      *)
  val constImp  : cid -> imp
  val constUni  : cid -> Uni

  (* Declaration Contexts *)

  val ctxDec    : dctx * int -> Dec	(* variable declaration       *)

  (* Explicit substitutions *)
    
  val id        : Sub			(* id                         *)
  val shift     : Sub			(* ^                          *)

  val bvarSub   : int * Sub -> Head     (* k[s]                       *)
  val headSub   : Head * Sub -> Head    (* H[s]                       *)
  val decSub    : Dec * Sub -> Dec	(* x:V[s]                     *)
    
  val comp      : Sub * Sub -> Sub	(* s o s'                     *)
  val dot1      : Sub -> Sub		(* 1 . (s o ^)                *)
  val ldot1     : Sub -> Sub		(* 1 .^ (s o ^)               *)

  (* EVar related functions *)

  val newEVar   : Exp -> Exp            (* creates X:V, []            *) 
  val newEVarCnstr : Exp * Eqn list -> Exp  (* creates X:V, Cnstr     *)
  val newTypeVar : unit -> Exp		(* creates X:type, []         *)

  (* Type related functions *)
  (* Eliminate targetFamOpt and targetFam -ic *)
  val targetFamList : Exp -> cid list option (* list of target type families *)
  val targetFamOpt : Exp -> cid option       (* target type family or NONE *)
  val targetFam : Exp -> cid                 (* target type family         *)
end;  (* signature INTSYN *)
