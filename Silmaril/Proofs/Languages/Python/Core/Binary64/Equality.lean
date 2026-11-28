module

public import Silmaril.Languages.Python.Core.Binary64.Defs
import Silmaril.Numeric.Ieee754.MaximumCorrectness

public section
namespace Silmaril.Proofs.Languages.Python.Core.Binary64

open Silmaril.Languages.Python.Core.Binary64
open Silmaril.Numeric.Ieee754 (F64 value64? finiteValue)

theorem finite_has_exact_value (value : F64.Finite) :
    ∃ q : ℚ, value.val.toRat? = some q := by
  have finite := value.property
  unfold F64.IsFinite at finite
  unfold F64.toRat? value64? finiteValue
  simp only [beq_iff_eq, finite, ite_false]
  split <;> exact ⟨_, rfl⟩

theorem equal_eq_ieee (left right : F64.Finite) :
    equal left right = true ↔ left.val.equal right.val = true := by
  obtain ⟨l, hl⟩ := finite_has_exact_value left
  obtain ⟨r, hr⟩ := finite_has_exact_value right
  simpa [equal, hl, hr] using (F64.equal_iff_of_toRat hl hr).symm

end Silmaril.Proofs.Languages.Python.Core.Binary64
