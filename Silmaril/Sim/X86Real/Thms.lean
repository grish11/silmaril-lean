module

public import Silmaril.Proofs.Sim.X86Real.Compose
public import Silmaril.Proofs.Sim.X86Real.Flags

/-!
# The tested x86-64 simulators, verified in Lean: results

Proofs in `Silmaril.Proofs.Sim.X86Real.{AccessG,Core,Compose,Flags}`; statements and the
quotations of `examples/wasm-sim/x86/x86-{g,m}.wat` in `Silmaril.Sim.X86Real.Defs`.

* `rgetG_total` … `fset6G_total`: the five state accessors of `simG` meet their contracts
  (total correctness, every profile and host relation).
* `core_of_accessors`: for every representation with `Rep.Laws`, the shared core (`$alu`,
  `i_alu_rr` for 64-bit add/sub/cmp) meets its contracts given the accessor contracts.
* **`iAluRR_G`**: `i_alu_rr` of the instantiated `simG` meets `iAluRRSpec (repG mi)`.
* **`aluFlags_add`**, **`aluFlags_sub`**: its flags are `Silmaril.X86.addFlags`/`subFlags`.

* `rgetM_total` … `fset6M_total`: the same for `simM` (byte-level, `user_regs_struct`).
* `fn_simM_core`: the core functions of `simM` are those of `simG` (`rfl`); **`iAluRR_M`**,
  **`iAluRR_GM`**: `i_alu_rr` of both representations meets the same contract.

Assumed: the instance facts `CodeOK sim I` (the instance runs the module's functions with their
types) and `Inst.Inj` (distinct addresses). Not covered: other methods, the decoder `step`.
-/

/-- info: 'Silmaril.Sim.X86Real.rgetG_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.rgetG_total

/-- info: 'Silmaril.Sim.X86Real.rsetG_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.rsetG_total

/-- info: 'Silmaril.Sim.X86Real.fgetG_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.fgetG_total

/-- info: 'Silmaril.Sim.X86Real.fsetG_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.fsetG_total

/-- info: 'Silmaril.Sim.X86Real.fset6G_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.fset6G_total

/-- info: 'Silmaril.Sim.X86Real.core_of_accessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.core_of_accessors

/-- info: 'Silmaril.Sim.X86Real.iAluRR_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.iAluRR_G

/-- info: 'Silmaril.Sim.X86Real.iAluRR_G_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.iAluRR_G_valid

/-- info: 'Silmaril.Sim.X86Real.aluFlags_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.aluFlags_add

/-- info: 'Silmaril.Sim.X86Real.aluFlags_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.aluFlags_sub

/-- info: 'Silmaril.Sim.X86Real.rgetM_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.rgetM_total

/-- info: 'Silmaril.Sim.X86Real.rsetM_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.rsetM_total

/-- info: 'Silmaril.Sim.X86Real.fgetM_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.fgetM_total

/-- info: 'Silmaril.Sim.X86Real.fsetM_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.fsetM_total

/-- info: 'Silmaril.Sim.X86Real.fset6M_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.fset6M_total

/-- info: 'Silmaril.Sim.X86Real.iAluRR_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.iAluRR_M

/-- info: 'Silmaril.Sim.X86Real.iAluRR_GM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.iAluRR_GM

/-- info: 'Silmaril.Sim.X86Real.fn_simM_core' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86Real.fn_simM_core

