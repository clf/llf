structure Sign' : SIGN =
   Sign (structure Basic = Basic
	 structure Term = Term
	 structure IPrint = ElfPrint  (* hack here *)
	 structure Print = ElfPrint);


Sign'.sig_print_full (Store.find_sig "cl-cutelim.elf");
