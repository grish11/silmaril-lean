module

public import Silmaril.Proofs.Sim.SysV.Desc
public import Silmaril.Proofs.Sim.SysV.Max
public import Silmaril.Proofs.Sim.SysV.Module
public import Silmaril.Proofs.Sim.SysV.Edge
public import Silmaril.Proofs.Sim.SysV.Add2

/-!
# The System V wrapper over the G simulator: results

Definitions in `Silmaril.Sim.SysV.Defs`; proofs in `Silmaril.Proofs.Sim.SysV.*`. Axioms: `propext`,
`Classical.choice`, `Quot.sound` only.

* **`decode_encode`**: descriptors round-trip through their byte encoding (the layout of
  `sysv.wat`).
* **`setup_abiEntry`**: the entry state built from a descriptor and any caller state meets
  `FnContract.AbiEntry` (`rsp ≡ 8 mod 16`, the sentinel readable at `[rsp]`).
* **`wrapper_sound`**: if the wrapper code (prologue, the G simulator's code of the body,
  epilogue), run from a store encoding the caller's registers with the arguments in its frame,
  returns status `0` and `r`, then the entry state meets `AbiEntry` and the function returns to
  the sentinel on the `Silmaril.X86.Ext` machine (`Ext.Returns`: the first `ret` to it) in a
  state meeting `FnContract.AbiReturn`, with `rax = r`.
* **`xgoal_of_wgoal`** (old name `reduce`): the Wasm problem `WGoal` solves the x86 problem `XGoal`; `reduction`,
  `instReduction`: as `Silmaril.Sim.Reduce.Reduction` / `Silmaril.Sim.Institution.Reduction` edges.
* **`wgoal_of_body`**: the wrapper's Wasm problem decomposes into the body's Wasm problem
  (`Silmaril.Sim.X86.G.WProblem`) plus glue conditions on registers and retirement.
* **`runExt_progress`**: translated bodies retire from every state with defined modelled flags.
* **`xgoal_of_body`**, `decomp`, `wrapperReduction`: for any G-fragment body and any number of
  stack arguments, the x86 problem from the body's Wasm problem plus two register glue facts
  (`PreGlue`, `PostGlue`; helpers `preGlue_true`, `postGlue_of_frame`, `entryCore_read`); as a
  `Reduce.Decomp` (DAG edge) and a `Reduce.Reduction`. `XGoal.of_flags`.
* **`add2_sysv`**: a second function through the generic edge (Wasm proof by `g_vc`, glue by
  `simp`).
* Open: `Task.stackArgPlaced`, `Task.gStackLoad` (reading stack arguments).
* **`max_sysv`**: `max` through the wrapper, end to end (Wasm solution by `wpc` ⇒ x86 contract).
* `sysvMaxModule_body`: the quoted WAT function is the generated wrapper code.
-/

/-- info: 'Silmaril.Sim.SysV.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.SysV.decode_encode

/-- info: 'Silmaril.Sim.SysV.setup_abiEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.SysV.setup_abiEntry

/-- info: 'Silmaril.Sim.SysV.wrapper_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.SysV.wrapper_sound

/-- info: 'Silmaril.Sim.SysV.xgoal_of_wgoal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.SysV.xgoal_of_wgoal

/-- info: 'Silmaril.Sim.SysV.wgoal_of_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.SysV.wgoal_of_body

/-- info: 'Silmaril.Sim.SysV.max_sysv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.SysV.max_sysv

/-- info: 'Silmaril.Sim.SysV.sysvMaxModule_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.SysV.sysvMaxModule_body

/-- info: 'Silmaril.Sim.SysV.xgoal_of_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.SysV.xgoal_of_body

/-- info: 'Silmaril.Sim.SysV.add2_sysv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.SysV.add2_sysv
