structure LexSyn = 
  LexSyn (structure IntSyn' = IntSyn)

structure LexPrint =
  LexPrint (structure LexSyn' = LexSyn
	      structure Formatter = Formatter)

structure Lex =
  Lex (structure Global = Global
       structure LexSyn' = LexSyn
       structure Order = Order
       structure LexPrint = LexPrint)
