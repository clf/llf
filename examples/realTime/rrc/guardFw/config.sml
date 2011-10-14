val rrc_guard_good = LLF.defineConfig
["examples/realTime/rrc/guardFw/nat.llf",
 "examples/realTime/rrc/guardFw/timers.llf",
 "examples/realTime/rrc/guardFw/rrc.llf",
 "examples/realTime/rrc/guardFw/good-test.llf",
 "examples/realTime/rrc/guardFw/rrc-rules.llf"];

val rrc_guard_bad = LLF.defineConfig
["examples/realTime/rrc/guardFw/nat.llf",
 "examples/realTime/rrc/guardFw/timers.llf",
 "examples/realTime/rrc/guardFw/rrc.llf",
 "examples/realTime/rrc/guardFw/bad-test.llf",
 "examples/realTime/rrc/guardFw/rrc-rules.llf"];
