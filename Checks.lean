import EvmOpt

/-- info: 'EvmOpt.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EvmOpt.run_sound

/-- info: 'EvmOpt.srun_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EvmOpt.srun_run

/-- info: 'EvmOpt.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EvmOpt.check_sound

/--
info: 'EvmOpt.optimizeWith_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms EvmOpt.optimizeWith_steps

/-- info: 'EvmOpt.xrun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EvmOpt.xrun_sound

/-- info: 'EvmOpt.xcheck_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EvmOpt.xcheck_steps
