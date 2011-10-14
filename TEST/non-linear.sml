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

use "examples/NON-LINEAR/ccc/config.sml";
cc ccc;
rd "examples/NON-LINEAR/ccc/examples.quy";

use "examples/NON-LINEAR/church-rosser/config.sml";
cc church_rosser;
rd "examples/NON-LINEAR/church-rosser/examples.quy";


use "examples/NON-LINEAR/compile/cls/config.sml";
cc compile_cls;
rd "examples/NON-LINEAR/compile/cls/examples.quy";

use "examples/NON-LINEAR/compile/cpm/config.sml";
cc compile_cpm;
rd "examples/NON-LINEAR/compile/cpm/examples.quy";

use "examples/NON-LINEAR/compile/cps/config.sml";
cc compile_cps;
rd "examples/NON-LINEAR/compile/cps/examples.quy";

use "examples/NON-LINEAR/compile/cxm/config.sml";
cc compile_cxm;
rd "examples/NON-LINEAR/compile/cxm/examples.quy";

use "examples/NON-LINEAR/compile/debruijn/config.sml";
cc compile_debruijn;
rd "examples/NON-LINEAR/compile/debruijn/examples.quy";

use "examples/NON-LINEAR/compile/debruijn1/config.sml";
cc compile_debruijn1;
rd "examples/NON-LINEAR/compile/debruijn1/examples.quy";


use "examples/NON-LINEAR/cut-elim/config.sml";
cc cut_elim;
rd "examples/NON-LINEAR/cut-elim/examples.quy";

use "examples/NON-LINEAR/lp/config.sml";
cc lp;
rd "examples/NON-LINEAR/lp/examples.quy";

use "examples/NON-LINEAR/lp-horn/config.sml";
cc lp_horn;
rd "examples/NON-LINEAR/lp-horn/examples.quy";

use "examples/NON-LINEAR/mini-ml/config.sml";
cc mini_ml;
rd "examples/NON-LINEAR/mini-ml/examples.quy";

use "examples/NON-LINEAR/prop-calc/config.sml";
cc prop_calc;
rd "examples/NON-LINEAR/prop-calc/examples.quy";

use "examples/NON-LINEAR/polylam/config.sml";
cc polylam;
rd "examples/NON-LINEAR/polylam/examples.quy";

use "examples/NON-LINEAR/units/config.sml";
cc units;
rd "examples/NON-LINEAR/units/examples.quy";
