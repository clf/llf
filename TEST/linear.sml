(* Global.chatter := 0; *)
(* Global.chatter := 1; *)
(* Global.chatter := 2; *)

fun cc (config) =
  case LLF.compileConfig (config)
    of LLF.OK => LLF.OK
     | LLF.ABORT => raise Domain;

fun rd (file) =
  case LLF.readFile (file)
    of LLF.OK => LLF.OK
     | LLF.ABORT => raise Domain;

(*

use "examples/games/iqblock/config.sml";
cc iqblock;
rd "examples/games/iqblock/examples.quy";
(* README missing *)

use "examples/games/mahjongg/config.sml";
cc socks;
rd "examples/games/mahjongg/examples.quy";

use "examples/languages/mlr/config.sml";
cc mlr;
rd "examples/languages/mlr/examples.quy";

use "examples/logics/ce-lhhf/config.sml";
cc ce_lhhf;
rd "examples/logics/ce-lhhf/examples.quy";

use "examples/logics/cll/config.sml";
cc cll;
rd "examples/logics/cll/examples.quy";

use "examples/logics/ill/config.sml";
cc ill;
rd "examples/logics/ill/examples.quy";

use "examples/logics/l-curry/config.sml";
cc l_curry;
rd "examples/logics/l-curry/examples.quy";

use "examples/logics/spine/config.sml";
cc spine;
rd "examples/logics/spine/examples.quy";

use "examples/misc/permutations/config.sml";
cc permutations;
rd "examples/misc/permutations/examples.quy";

use "examples/planning/blocks/config.sml";
cc blocks;
rd "examples/planning/blocks/examples.quy";

use "examples/processors/x86/config.sml";
cc x86_iter;
rd "examples/processors/x86/examples-iter.quy";
cc x86_rec;
rd "examples/processors/x86/examples-rec.quy";

use "examples/security/ns/config.sml";
cc ns;
rd "examples/security/ns/examples.quy";

use "examples/realTime/rrc/fw/config.sml";
cc rrc_fw_good;
rd "examples/realTime/rrc/fw/examples.quy";
cc rrc_fw_bad;
rd "examples/realTime/rrc/fw/examples.quy";

use "examples/realTime/rrc/guardFw/config.sml";
cc rrc_guard_good;
rd "examples/realTime/rrc/guardFw/examples.quy";
cc rrc_guard_bad;
rd "examples/realTime/rrc/guardFw/examples.quy";

use "examples/realTime/rrc/metaFw/config.sml";
cc rrc_meta_good;
rd "examples/realTime/rrc/metaFw/examples.quy";
cc rrc_meta_bad;
rd "examples/realTime/rrc/metaFw/examples.quy";

use "examples/realTime/rrc/varFw/config.sml";
cc rrc_var_good;
rd "examples/realTime/rrc/varFw/examples.quy";
cc rrc_var_bad;
rd "examples/realTime/rrc/varFw/examples.quy";

*)

use "examples/logics/turing/config.sml";
(* cc tm_adder; *)
(* rd "examples/logics/turing/example-adder.quy"; *)
cc tm_copier;
rd "examples/logics/turing/example-copier.quy";
