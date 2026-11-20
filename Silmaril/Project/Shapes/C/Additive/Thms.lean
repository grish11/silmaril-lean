module

public import Silmaril.Project.Shapes.C.Additive.Defs

/-!
# The additive constraint: theorems

* `AdditiveOperands.not_ptr_ptr`: two `int *` operands violate C11 §6.5.6¶2 (no pointer is an
  arithmetic or integer type).
* `AdditiveOperands.ptr_int`: `int *` plus `int` satisfies it.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.C

/-- **Pointer plus pointer is a constraint violation** (`int *` + `int *`). -/
theorem AdditiveOperands.not_ptr_ptr : ¬ AdditiveOperands intPtrCtype intPtrCtype := by
  rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩) <;> exact h

/-- Pointer plus integer satisfies the constraint. -/
theorem AdditiveOperands.ptr_int : AdditiveOperands intPtrCtype intCtype := .ptrInt trivial trivial

end Silmaril.Project.Shapes.C

end
