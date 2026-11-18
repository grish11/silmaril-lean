module

public import Silmaril.Proofs.Sim.Reduce.Toy.F

/-!
# The toy's `f`, decomposed: results

`f` (push/push/sub/mov/**call sum_to**/mov/mov/**call dbl**/add/add/pop/pop/ret) is solved by
**per-function decomposition** (assume-guarantee): the calls leave `f`'s Wasm dispatcher
(`fTab b` holds only `f`'s instructions), so `f` becomes three **Wasm pieces**, one per segment
between calls, and the callees enter only through their **already solved ISA contracts**.

* Wasm pieces (pure Wasm statements, cut points of the dispatcher with a measure):
  `EntriesA` (entry to `call sum_to`), `EntriesB` (return of `sum_to` to `call dbl`), `EntriesC`
  (return of `dbl` to `ret`); solved by `entriesA_sol`, `entriesB_sol`, `entriesC_sol`;
* generic glue (proved once): `LProblemMB`/`reduce_loopMB` (the Wasm problem with the final
  window bytes, transferred to the x86 problem with final loads), `progressM_nf` (progress of
  flag-free instructions with memory), `ld_of_loadN`, `loadN_keep`, `winOK_keep`,
  `tabAt_of_loaded`, `segment` (run existence + post of one segment);
* **`isa_f_of : EntriesA → EntriesB → EntriesC → isaGoal .sumTo → isaGoal .dbl → isaGoal .f`**:
  the composition (callee contracts: `AbiEntry` from the pushed return address, `Entered` from
  the loaded code outside the window, `Spec.Result` for registers and the unchanged memory);
* **`isa_f : Toy.isaGoal .f`**: the System V contract of the toy's `f` on `Open9.isa`, at
  every placement, with the stack window as footprint.
-/

/-- info: 'Silmaril.Sim.Reduce.Toy.F.isa_f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.Toy.F.isa_f
