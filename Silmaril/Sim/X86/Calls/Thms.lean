module

public import Silmaril.Proofs.Sim.X86.Calls.Max

/-!
# The P-calls `max` of the G simulator, verified modularly: results

* `mov_valid`, `cmp_valid`, `cmovl_valid`, `next_valid`: the quoted methods of
  `Silmaril.Sim.X86.G.simModule` meet their Wasm-level specifications `mspec` (`wat_vc` over a
  symbolic store: the globals frame rule of `Silmaril.Wasm.Logic.VC.globalVal_setGlobalIdx_ne`);
* **`max_valid_of`**: the P-calls program `max` (a body of `call`s only) meets `maxSpec` from
  the **specifications** of the methods (spec context `maxSpecs`, `wpc`'s modular call rule);
* **`max_valid`**: the two combined, for any instance whose functions `0, 4, 5, 6, 7` are the
  quoted code (`IsMethod`) at distinct addresses and whose globals are distinct;
* **`max_regs`**: the resulting global file has `rax` = signed max of `rdi`, `rsi`, RIP + 10,
  the other GPRs unchanged.

Every profile and host relation. Proofs in `Silmaril.Proofs.Sim.X86.Calls.Max`.
-/

/-- info: 'Silmaril.Sim.X86.Calls.max_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.Calls.max_valid

/-- info: 'Silmaril.Sim.X86.Calls.max_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.Calls.max_regs
