module

public import Silmaril.Proofs.Sim.X86.Toy.Contract

/-!
# The reduction toy `f` (push/call/pop/ret, a loop, two callees): results

* `toy_entries`: every dispatcher entry, by Wasm cut points with a measure;
* `wasm_solution` (Wasm problem, `LProblemM`), **`x86_solution`** (x86 problem, by
  `xlproblemM_of_lproblemM`);
* **`toyContract : FnContract Open9.isa`** (`toySpec_total`): from every System V entry with the
  toy's bytes (as linked in `toy.elf`) at `rip - 0x1d` and a 40-byte stack window, the open
  machine returns to the caller with `rax = (0 + ⋯ + rdi) + 2·rsi`, callee-saved registers
  restored, memory written only in the window.
-/

/-- info: 'Silmaril.Sim.X86.Toy.toySpec_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.Toy.toySpec_total
