module

public import Silmaril.Proofs.Sim.X86.GM.Run
public import Silmaril.Proofs.Sim.X86.GM.WStep

/-!
# The G simulator with memory (GM): results

Proofs in `Silmaril.Proofs.Sim.X86.GM.*`; every profile, every host relation.

* **`MemEnc.load`**, **`MemEnc.store`**: in the guest window (Wasm memory 0, offset `- lo`), x86
  and Wasm 64-bit accesses agree; stores keep the abstraction and write only inside the window
  (`Silmaril.Process.Memory.WritesWithin`, the `FnContract` footprint form);
* `exec_wrap`: the `i32` address from the `i64` one, bit by bit (no `i32.wrap_i64` in `exec1`);
* **`emitM_sound`**: `mov r64,[m]`, `mov [m],r64` (`[base + index·2^s + disp]`), `push`, `pop`,
  `call rel32`, `ret`, `op r64, imm8/imm32`, all register/jump forms, and the width-generic
  forms (`Silmaril.Proofs.Sim.X86.GM.Form`): `movzx`/`movsx` 8/16 → 32/64, `mov r32, [m]`,
  `movsxd`, `cmp`/`test` at 8, 32, 64 bits with register, immediate or memory operands,
  `op r64, [m]` (all six ALU operations), `nop`. Read-only windows (`Win.rw = false`) have no
  store, push or call methods;
  **`emitM_holds`**: a method that evaluates made its access inside the window (the Wasm code
  checks it, trapping otherwise); `emitM_progress`;
* dispatcher with memory: `xrun_twpM`, **`xlproblemM_of_lproblemM`** (`LProblemM` ⇒ `XLProblemM`),
  **`xrun_existsM`** (termination from a Wasm measure), **`run_of_xrunM`** (runs of the open
  machine `Silmaril.Machine.X86.Open.step`, `ret` included);
* Wasm-level stack methods: `push_wstep`, `pop_wstep`, `call_wstep`, `ret_wstep`.
-/

/-- info: 'Silmaril.Sim.X86.GM.emitM_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.GM.emitM_sound

/-- info: 'Silmaril.Sim.X86.GM.form_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.GM.form_exec

/-- info: 'Silmaril.Sim.X86.GM.form_wasm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.GM.form_wasm

/-- info: 'Silmaril.Sim.X86.GM.xlproblemM_of_lproblemM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.GM.xlproblemM_of_lproblemM
