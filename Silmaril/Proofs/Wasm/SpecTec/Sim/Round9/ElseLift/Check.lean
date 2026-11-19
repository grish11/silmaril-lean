module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.Defs

/-!
# Round 9, REH: the earlier rules of the `otherwise` pairs pass the forward check

`fwdPairs_fixed` (`decide +kernel`): in the fixed wasm-3.0 script, at every pair `(i, j)` of
`ElseBwd.elsePairs`, rule `j` of `Step_read` passes `ElseBwd.goodRuleE`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The earlier rule of every `otherwise` pair passes `goodRuleE`.** -/
theorem fwdPairs_fixed : fwdPairsIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift
