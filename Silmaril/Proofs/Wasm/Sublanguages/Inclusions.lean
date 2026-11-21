module

public import Silmaril.Wasm.Sublanguages.Defs

public section

namespace Silmaril.Wasm.Sublanguages.Proofs

theorem inclusion_unique {A B : Language} (left right : Inclusion A B) : left = right := by
  obtain ⟨leftI, leftF, leftM, hi, hf, hm⟩ := left
  obtain ⟨rightI, rightF, rightM, hi', hf', hm'⟩ := right
  have instrEq : leftI = rightI := funext fun source => B.toInstr.injective ((hi source).trans (hi' source).symm)
  have funcEq : leftF = rightF := funext fun source => B.toFunc.injective ((hf source).trans (hf' source).symm)
  have modEq : leftM = rightM := funext fun source => B.toModule.injective ((hm source).trans (hm' source).symm)
  subst rightI; subst rightF; subst rightM; rfl

end Silmaril.Wasm.Sublanguages.Proofs
