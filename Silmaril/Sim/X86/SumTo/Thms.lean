module

public import Silmaril.Proofs.Sim.X86.SumTo.X86
public import Silmaril.Proofs.Sim.X86.SumTo.Total

/-!
# `sum_to` through the Wasm dispatcher: results

* `wasm_solution`: the Wasm problem, by the cut-point rule `dispatch_hwp`, six straight-line
  entry lemmas evaluated by `simp`, and one arithmetic lemma (`tri_step`);
* **`x86_solution`**: the x86 problem (`XLProblem (sumTab b) …`), by `xlproblem_of_lproblem`;
* **`sum_returns`**: every run of the bytes `sumBytes` (as assembled by GNU `as` from
  `examples/wasm-sim/x86/tests/funcs.S`) on the `Silmaril.X86.Ext` machine that returns to the address at `[rsp]`
  returns with `rax = 0 + 1 + ⋯ + rdi` modulo `2^64` (partial correctness);
* `measured_step`, `sum_exists`: termination from a Wasm-level measure (`xrun_exists`);
* **`sumContract : FnContract Open9.isa`** (`sumSpec_total`): total correctness in the
  recommended contract form.
-/

/-- info: 'Silmaril.Sim.X86.SumTo.sum_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.SumTo.sum_returns

/-- info: 'Silmaril.Sim.X86.SumTo.sumSpec_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.SumTo.sumSpec_total
