module

public import Silmaril.Proofs.Sim.RV64.Reduce.Sound
public import Silmaril.Proofs.Sim.RV64.Reduce.Spec

/-!
# Reducing RV64 problems to Wasm problems: results

Proofs in `Silmaril.Proofs.Sim.RV64.Reduce.Sound`, every profile and every host relation:

* **`reduce`**: a solution of the Wasm problem `WasmRun P host fi a ma mt I n` (`n + 1`
  partial-correctness triples about the export `step` of the concrete module) gives, from every
  store holding `step` and memory bytes `B` with `I 0 B`, the RV64 fact
  `Halts (absCode B) (absState B) n (absState B')` with `I n B'`: the reference machine
  (`Silmaril.RiscV.decode`/`step` on the fetched words) halts after exactly `n` steps;
* `step_run`, `step_triple`: one call of `step` returns, and its result satisfies both
  `StepPost` (soundness) and any user triple about it.
-/
