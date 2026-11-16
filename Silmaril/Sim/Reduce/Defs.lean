module

public import Silmaril.Sim.Reduce.Core.Defs
public import Silmaril.Sim.Reduce.X86.Defs

/-!
# Reducing ISA problems to Wasm problems (definitions, umbrella)

Re-exports the ISA-agnostic core `Silmaril.Sim.Reduce.Core` (the reduction record `Decomp`, the
run-level simulator interface `SoundSim`, `IsaReach`, `WasmTotal`, the decomposition shapes) and
the x86-64 System V instance `Silmaril.Sim.Reduce.X86` (`specPre`, `specPost`, `specWasm`). Guide:
`docs/projects/wasm-sim-reduction.md`.
-/
