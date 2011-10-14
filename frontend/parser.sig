(* Top-Level Parser *)
(* Author: Frank Pfenning *)

signature PARSER =
sig

  structure Parsing : PARSING
  structure Stream : STREAM
  structure ExtSyn : EXTSYN
  structure ExtSynQ : EXTSYN
  structure Names : NAMES
  structure ExtModes : EXTMODES
  structure LexSynExt : LEXSYNEXT

  datatype fileParseResult =
      (* c : A  or  c = M : A *)
      SgnEntry of ExtSyn.sgnentry * ExtSyn.Paths.region
(*    | LinEntry of ExtSyn.linentry * ExtSyn.Paths.region       -ic *)
    | FixDecl of (ExtSyn.name * ExtSyn.Paths.region) * Names.Fixity.fixity
    | NamePref of (ExtSyn.name * ExtSyn.Paths.region) * ExtSyn.name  
    | ModeDecl of ExtModes.termM
    | LexDecl of LexSynExt.term
    | Query of int option * int option * ExtSynQ.term (* expected, try, A *)
    (* Further pragmas to be added later here *)

  val parseFile: TextIO.instream -> fileParseResult Stream.stream
  val parseQuery : string * string -> ExtSynQ.term Stream.stream

end;  (* signature PARSER *)
