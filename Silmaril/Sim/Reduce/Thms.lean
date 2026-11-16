module

public import Silmaril.Sim.Reduce.Defs
public import Silmaril.Sim.Reduce.Core.Thms
public import Silmaril.Sim.Reduce.X86.Thms

/-!
# Reducing ISA problems to Wasm problems (results, umbrella)

Re-exports `Silmaril.Sim.Reduce.Core.Thms` (decompositions, the reduction theorem
`isaReach_of_wasmTotal`, counterexample transfer, `SoundSim.ofSimulation` and
`SoundSim.ofExportCert`, assume-guarantee and cut-point composition) and
`Silmaril.Sim.Reduce.X86.Thms` (`spec_total_iff`, `specReduction`, `specExact`).
-/
