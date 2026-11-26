module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Fuel.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Fuel.Correctness

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic

universe v w

variable {V K α : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

/-- A finite successful run of the actual store semantics is attained at
some finite executable budget, including the full final store. -/
theorem mem_run_iff_runFuel (m : Model F Option α) (cfg : CFG V K F)
    (store : V → α) (output : Transfer V K α) :
    output ∈ Cyclic.run (toPartModel m) cfg store ↔ ∃ fuel, runFuel m cfg fuel store = some output :=
  Fuel.Proofs.mem_run_iff m cfg store output

end Silmaril.SSA.LambdaRTL.CFG.Cyclic
