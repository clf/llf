(* Some files here use polymorphism, which is not supported *)

val ccc =
  FrontEnd.defineConfig
  ["examples/NON-LINEAR/ccc/ccc.elf",
   "examples/NON-LINEAR/ccc/lambda.elf",
   "examples/NON-LINEAR/ccc/catlem.elf", 
   "examples/NON-LINEAR/ccc/cong.elf", 
   "examples/NON-LINEAR/ccc/abs-env.elf", 
   (* "examples/NON-LINEAR/ccc/subext.elf", *)
   (* "examples/NON-LINEAR/ccc/eqpres1.elf", *)
   "examples/NON-LINEAR/ccc/conc.elf", 
   "examples/NON-LINEAR/ccc/eqpres2.elf",
   "examples/NON-LINEAR/ccc/inv1.elf"
   (* "examples/NON-LINEAR/ccc/inv2.elf", *)
   (* "examples/NON-LINEAR/ccc/refl.elf" *)];
