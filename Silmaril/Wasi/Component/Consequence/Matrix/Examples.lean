module

public import Silmaril.Wasi.Component.Consequence.Matrix.Defs

/-! # The interpretation matrix: well-formedness

The matrix is regular (`cells_length`: 4 protocols × 6 states × 2 boundaries), and exactly the
one-shot cells of the one-shot protocols and the stateful cells of the stateful protocols are
supported (`supported_iff`). Kernel evaluation (`decide`).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence.Matrix

theorem cells_length : cells.length = 48 := by decide

/-- **Supported exactly where the protocol and the state shape agree.** -/
theorem supported_iff (p : Protocol) (s : StateShape) (b : Boundary) :
    (cell p s b).supported = (p.stateful == (s != .oneShot)) := by
  cases p <;> cases s <;> cases b <;> rfl

theorem supported_count : (cells.filter Cell.supported).length = 24 := by decide

/-- The cells with specification-strategy evidence: protocol 1 (both boundary cells) and
protocol 2 with the list policy at the call boundary. -/
theorem specStrategy_count :
    (cells.filter fun c => match c.support with
      | .supported _ _ _ .specStrategy => true
      | _ => false).length = 3 := by decide

end Silmaril.Wasi.Consequence.Matrix
