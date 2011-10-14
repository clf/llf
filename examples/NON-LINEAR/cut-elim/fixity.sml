local open Fixity
in
 val _ = installFixity("and",Infix(11,Right))
 val _ = installFixity("imp",Infix(10,Right))
 val _ = installFixity("or",Infix(11,Right))
 val _ = installFixity("not",Prefix(12))
end
