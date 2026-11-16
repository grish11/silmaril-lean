module

public import Silmaril.Proofs.Sim.X86.Loop.Hoare
public import Silmaril.Proofs.Sim.X86.Loop.Machine
public import Silmaril.Proofs.Sim.X86.Loop.Total

/-!
# Control flow through the dispatcher: results

Proofs in `Silmaril.Proofs.Sim.X86.Loop.*` (and `Silmaril.Proofs.Sim.X86.G.Jump` for `jcc`/`jmp`);
every profile, every host relation.

* `emitX_sound`: the methods, jumps included, are sound against `Silmaril.X86.Ext.exec`;
* `xrun_twp`: an `XRun` of a table is matched, in every run of the dispatcher (`TWP`), by a
  store encoding the final state;
* **`xlproblem_of_lproblem`**: `LProblem` (Wasm, partial correctness) of `dispCode (compileTab tab)`
  solves `XLProblem tab` (x86);
* **`dispatch_hwp`** (cut-point rule): Wasm problems of dispatchers reduce to one
  straight-line Wasm problem per entry under an invariant;
* `xrun_of_run`: machine runs (`Ext.stepOpt`) through code placed in memory (`TabAt`) that
  end with a return are `XRun`s; `run_of_xrun` the converse;
* **`xrun_exists`**: termination of the x86 code from a measured Wasm invariant (the
  hypotheses of `dispatch_twp`) and x86 progress.
-/

/-- info: 'Silmaril.Sim.X86.Loop.xlproblem_of_lproblem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.Loop.xlproblem_of_lproblem

/-- info: 'Silmaril.Sim.X86.Loop.dispatch_hwp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.Loop.dispatch_hwp

/-- info: 'Silmaril.Sim.X86.Loop.xrun_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.Loop.xrun_of_run
