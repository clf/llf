(* Parsing Signature Entries *) 
(* Author: Frank Pfenning *)

signature PARSE_ENTRY =
sig

  structure Parsing : PARSING
  structure ExtSyn : EXTSYN

  val parseSgnEntry' : ExtSyn.sgnentry Parsing.parser

end;  (* signature PARSE_ENTRY *)
