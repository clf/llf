val rrc_fw_good = LLF.defineConfig
["examples/realTime/rrc/fw/nat.llf",
 "examples/realTime/rrc/fw/timers.llf",
 "examples/realTime/rrc/fw/rrc.llf",
 "examples/realTime/rrc/fw/good-test.llf",
 "examples/realTime/rrc/fw/rrc-rules.llf"];

val rrc_fw_bad = LLF.defineConfig
["examples/realTime/rrc/fw/nat.llf",
 "examples/realTime/rrc/fw/timers.llf",
 "examples/realTime/rrc/fw/rrc.llf",
 "examples/realTime/rrc/fw/bad-test.llf",
 "examples/realTime/rrc/fw/rrc-rules.llf"];
