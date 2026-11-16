module

public import Silmaril.Wasi.Component.Consequence.Signed.Matrix.Defs

/-! # Coverage of the signed and two-sided protocols: well-formedness

Every variant has one cell (`cells_length`, `variant_cell`). Two cells rest on specification
strategies, two on Core execution, and eight on definitions with general laws
(`count_specStrategy`, `count_execution`, `count_definitions`). Kernel evaluation (`decide`).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence.SignedMatrix

theorem cells_length : cells.length = 12 := by decide

theorem variant_cell (v : Variant) : (cell v).variant = v := by
  rcases v with ⟨_ | _, _ | _⟩ | _ | _ | _ | _ | ⟨_ | _, _ | _⟩ <;> rfl

theorem count_specStrategy : (cells.filter (·.evidence == .specStrategy)).length = 2 := by decide
theorem count_execution : (cells.filter (·.evidence == .execution)).length = 2 := by decide
theorem count_definitions : (cells.filter (·.evidence == .definitions)).length = 8 := by decide

end Silmaril.Wasi.Consequence.SignedMatrix
