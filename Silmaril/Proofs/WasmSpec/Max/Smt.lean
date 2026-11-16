module

public import Silmaril.Proofs.WasmSpec.Max.Tactic
import Std.Tactic.BVDecide

/-!
# `Max` v1, mode `tactic+smt`

`vcs_smt : VCs`, each branch condition by `bv_decide`, and
`spec_smt := spec_of_vcs vcs_smt` with the reduction of mode `tactic`. Trust:
whatever auxiliary axioms `bv_decide` adds (audited in `Silmaril.WasmSpec.Max.Thms`).
-/

@[expose] public section

namespace Silmaril.WasmSpec.Max

/-- `VCs` by SAT. -/
theorem vcs_smt : VCs where
  then_ x y h := by
    unfold smax
    bv_decide
  else_ x y h := by
    unfold smax
    bv_decide

/-- Mode `tactic+smt`. -/
theorem spec_smt : Spec := spec_of_vcs vcs_smt

end Silmaril.WasmSpec.Max
