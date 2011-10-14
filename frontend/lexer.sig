(* Lexer *)
(* Author: Frank Pfenning *)

signature LEXER =
sig

  (* Stream is not memoizing for efficiency *)
  structure Stream : STREAM
  structure Paths : PATHS

  datatype IdCase =
      Upper				(* [A-Z]<id> or _<id> *)
    | Lower				(* any other <id> *)
    | Quoted				(* '<id>' *)

  datatype Token =
      EOF				(* end of file or stream, also `%.' *)
    | DOT				(* `.' *)
    | COLON				(* `:' *)
    | HAT                               (* `^' *)
    | LPAREN | RPAREN			(* `(' `)' *)
    | LBRACKET | RBRACKET		(* `[' `]' *)
    | LBRACE | RBRACE			(* `{' `}' *)
    | BACKARROW | ARROW			(* `<-' `->' *)
    | BACKLOLLI | LOLLI                 (* `o-' `-o' *)
    | WITH                              (* `&' *)
    | TOP                               (* `<T>' *)
    | COMMA                             (* `,' *)
    | FST                               (* `<fst>' *)
    | SND                               (* `<snd>' *)
    | UNIT                              (* `()' *)
    | TYPE				(* `type' *)
    | EQUAL				(* `=' *)
    | ID of IdCase * string		(* identifer *)
    | UNDERSCORE			(* `_' *)
    | INFIX | PREFIX | POSTFIX		(* `%infix' `%prefix' `%postfix' *)
    | NAME				(* `%name' *)
    | QUERY				(* `%query' *)
    | MODE				(* `%mode' *)
    | LEX				(* `%lex' *)

  exception Error of string

  (* lexer returns an infinite stream, terminated by EOF token *)
  val lexStream : TextIO.instream -> (Token * Paths.region) Stream.stream
  val lexTerminal : string * string -> (Token * Paths.region) Stream.stream
  (*
  val lexString : string -> (Token * Paths.region) Stream.stream
  *)

  val toString : Token -> string

  (* Utilities *) 
  exception NotDigit of char
  val stringToNat : string -> int
end;  (* signature LEXER *)
