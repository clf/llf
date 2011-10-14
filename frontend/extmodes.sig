(* External Syntax of Mode Declarations *)
(* Author: Carsten Schuermann *)

signature EXTMODES =
sig
  structure ExtSyn : EXTSYN 
  structure Paths : PATHS 

  type mode

  val plusplus  : Paths.region -> mode
  val plus      : Paths.region -> mode
  val star      : Paths.region -> mode
  val minus     : Paths.region -> mode
  val minusminus: Paths.region -> mode

  type termIm
  type spineIm

  val nilIm : Paths.region -> spineIm
  val appIm : (mode * ExtSyn.name option) * spineIm -> spineIm 
  val rootIm: ExtSyn.name * Paths.region * spineIm -> termIm

  type termEx

  val rootEx : ExtSyn.term * Paths.region -> termEx
  val piEx : mode * ExtSyn.decl * termEx -> termEx

  type termM 
  val explicit : termEx -> termM
  val implicit : termIm -> termM
end;  (* signature EXTMODES *)


signature MODE_RECON =
sig
  structure Modes  : MODES
  include EXTMODES

  exception Error of string
  val modeToMode : termM -> IntSyn.cid * Modes.ModeSpine
end;  (* signature MODE_RECON *)
