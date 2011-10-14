functor Parsing
  (structure Stream' : STREAM
   structure Lexer' : LEXER
     sharing Lexer'.Stream = Stream')
     : PARSING
  (* :> PARSING
        where Stream = Stream'
        where Lexer = Lexer'
  *) =
struct

  structure Stream = Stream'
  structure Lexer = Lexer'

  type lexResult = Lexer.Token * Lexer.Paths.region

  type 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front

  exception Error of string
  fun error (r, msg) =
      raise Error (Lexer.Paths.toString r ^ " " ^ "Error:\n" ^ msg)

end;  (* functor Parsing *)
