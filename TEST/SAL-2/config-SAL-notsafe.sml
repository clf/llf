val REG = FrontEnd.defineConfig [
"binary.llf",
"regflag-notsafe.llf",
"SAL-notsafe.llf",
"state.llf",
"state2.llf",
"safe.llf"];

FrontEnd.compileConfig REG;

FrontEnd.top ();
