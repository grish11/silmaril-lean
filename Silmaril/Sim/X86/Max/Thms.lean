module

public import Silmaril.Proofs.Sim.X86.Max.X86
public import Silmaril.Proofs.Sim.X86.Max.Contract

/-!
# `max` through the Wasm simulator: results

* `wasm_solution`: the Wasm problem (`WProblem … maxCode`), by the generator `wpc` (`g_vc`)
  and one bit-vector lemma (`max_bits`);
* **`x86_solution`**: the x86 problem (`XProblem maxProg`), by `Silmaril.Sim.X86.G.xproblem_of_wproblem`;
* **`max_returns`**: on the `Silmaril.X86.Ext` machine, the bytes `maxBytes` at RIP with a
  return address `exit` at `[rsp]` return to `exit` with `rax` the signed maximum of `rdi`
  and `rsi` and the other registers (but `rsp`) unchanged.
* **`maxContract : FnContract Open9.isa`** (`maxSpec_total`): `max` in the recommended
  contract form (System V entry/return, empty footprint, `rax` = signed maximum).

Proofs in `Silmaril.Proofs.Sim.X86.Max.*`.
-/

/-- info: 'Silmaril.Sim.X86.Max.max_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.Max.max_returns

/-- info: 'Silmaril.Sim.X86.Max.maxSpec_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.Max.maxSpec_total
