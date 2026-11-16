module

public import Silmaril.Sim.Wasm.Defs
public import Silmaril.Proofs.Sim.Wasm.Bridge

/-!
# Wasm simulators: the bridge interface, what is proved (header)

PROVED (proofs in `Silmaril/Proofs/Sim/Wasm/Bridge.lean`, names in `Silmaril.Sim.Wasm.ExportSim`), for
every profile `P` and every host relation `host` fixed in the `ExportSim`:

* **`Cert.simulation`**: a certificate is a `Silmaril.Sim.Simulation K.toMachine B`; `Cert.sound`
  (`Silmaril.Sim.Sound`). From there `Simulation.sem`, `Simulation.angelic`,
  `Simulation.reaches`, `Silmaril.Sim.Institution.transfer` and
  `Silmaril.Sim.Reduce.SoundSim.ofExportCert` apply with no further glue. `Cert.obligations`
  gives the derived `WasmSim.Obligations` form.
* `methodOK_of_fspecValid`, `methodOK_of_fspecValidU`: every-run triples
  (`Silmaril.Wasm.Logic.Hoare.FSpecValid`) of the method's export give per-method soundness
  (through `FSpecValid.invoke_vals`);
* `methodOK_of_ctxSat` (same-module accessors, code substitution by contracts): the core's
  method contexts valid relative to the accessor contexts (`Hoare.CtxSat`), plus the accessor
  contexts valid for this module's bodies (`ctx_valid_of_each`: one triple per accessor);
* `reduction` (soundness → view, loading and one per-method problem per command) and
  `reductionCore` (soundness → view, loading, the shared core problem, one per accessor), as
  goal-indexed `Silmaril.Sim.Institution.Reduction`s (`Silmaril.Sim.Reduce.Decomp.ofReduction`
  turns them into `Decomp`s).

Further adapters: `Silmaril.Sim.Wasm.FnSpec` (`methodOK_of_vc`) and `Silmaril.Sim.Wasm.Open`
(`methodOK_of_moduleSat`, `methodOK_of_core`).

Not proved here: that `get` agrees with the module's `get` export, or that a concrete module
instantiates to stores satisfying `R` (`instantiateOnce?`); both are per-simulator facts.
-/
