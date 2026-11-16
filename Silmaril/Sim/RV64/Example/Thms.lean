module

public import Silmaril.Proofs.Sim.RV64.Example.Main

/-!
# An RV64 problem solved as a Wasm problem: results

Proofs in `Silmaril.Proofs.Sim.RV64.Example.{Fast,Main}`:

* **`prog_spec`** (the RV64 problem): for every RV64 state `σ` at `pc = 0x1000`, the reference
  machine (`Silmaril.RiscV.decode`/`step` on the words of `prog` = `add a0,a0,a1;
  addi a0,a0,1` at `0x1000`) halts after exactly two steps with `a0 = a0₀ + a1₀ + 1` and
  `pc = 0x1008`;
* **`wasm_solution`** (the Wasm problem): three Hoare triples about the export `step` of the
  simulator module, at every profile and host relation, from `post_add`/`post_addi`/`post_stop`
  (through the specialised semantics of `step`, proved once in `step_sound`; seconds per instruction);
* the transport is `Silmaril.Sim.RV64.Reduce.reduce`, with the instantiated module (`sim_funcs`,
  `sim_mems`) and the memory image `img σ prog`.
-/
