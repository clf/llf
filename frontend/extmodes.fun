(* External Syntax of Mode Declarations *)
(* Author: Carsten Schuermann *)

functor ExtModes (structure ExtSyn : EXTSYN) : MODE_RECOND =
struct
  open ExtSyn

  datatype mode =
      plusplus 
    | plus
    | star
    | minus
    | minusminus

  datatype mterm =
      mroot of string * mspine
    | mpi of mdecl * mterm

  and mspine =
      mnil 
    | mapp of marg * mspine 

  and marg = 
      marg of mode option * name
      
  and mdecl =
    mdecl of mode option * name * term

end; (* functor ExtSyn *)


