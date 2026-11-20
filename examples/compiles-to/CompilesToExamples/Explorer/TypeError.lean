module

public import Silmaril.Project.Shapes.C.Additive.Thms
public import Silmaril.Project.Shapes.C.Defs
public meta import Silmaril.Project.Shapes.C.Defs
import all Init.Data.String.Legacy
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap

/-!
# A type-error certificate under a restricted judgment

The kernel checks both the operand types extracted from the exact source by `AdditionFragment`
and their violation of C11 §6.5.6¶2. This is not a proof about the general Cerberus frontend.
-/

@[expose] public section

namespace CompilesToExamples.Explorer.TypeError

open Silmaril.Project.Shapes.C

/-- The C text, verbatim. -/
abbrev cText : String :=
  "int *addp(int *p, int *q)\n{\n  return p + q;\n}\n"

-- The frontend does not decide this program (compiled evaluation, not a proof).
#guard match FrontendAil cText with
  | .error e => e == "typing: Silmaril: typing not yet ported: binary operands (§6.5.5-6.5.12)"
  | .ok _ => false

/-- **The operands of `p + q` (`int *`, `int *`) violate C11 §6.5.6¶2.** -/
theorem addp_operands : ¬ AdditiveOperands intPtrCtype intPtrCtype := AdditiveOperands.not_ptr_ptr

/-- The exact text is recognized and both operands are parameters of type `int *`. -/
theorem addp_parses : AdditionFragment.operands cText = some (intPtrCtype, intPtrCtype) := by
  cbv

/-- The recognized source text fails the additive constraint, not a frontend diagnostic. -/
theorem addp_type_error : ¬ AdditionFragment.Accepts cText := by
  rintro ⟨pair, parsed, valid⟩
  rw [addp_parses] at parsed; cases parsed; exact addp_operands valid

/-- Replacing the second pointer with an integer satisfies the same judgment. -/
theorem addp_int_accepted : AdditionFragment.Accepts "int *addp(int *p, int q) { return p + q; }" :=
  ⟨(intPtrCtype, intCtype), by cbv, AdditiveOperands.ptr_int⟩

end CompilesToExamples.Explorer.TypeError

end
