module

public import Silmaril.Proofs.Sim.GlibcBridge.Steps

/-!
# The import call as Wasm code: results

* **`ext_steps`**: the import call's method `extCode0` (argument globals, `call ext.call`,
  `rax :=` result, scratch `:= nd.undef`) is a run of the Wasm small-step semantics
  (`Silmaril.Wasm.Execution.Core.Step`) from `s` to `extStore0 s f v ws`, with `ext.call` a host
  function answering as the contract admits (`extHost C mem`).
* **`ext_ret_steps`**: followed by GM's `ret` method, it reaches the store `BRun.ext` continues
  from: the dispatcher's `ext` step is a Wasm run.
-/

/-- info: 'Silmaril.Sim.GlibcBridge.ext_ret_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.GlibcBridge.ext_ret_steps
