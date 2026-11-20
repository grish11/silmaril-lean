module
public import Silmaril.Formats.PER.NormalForm.Defs
import Silmaril.Proofs.Formats.PER.NormalForm.Basic

public section
namespace Silmaril.Formats.PER
variable {α : Type} {R : PER α} {selected : α → Prop}

theorem normalForm_iff_discrete : R.NormalForm selected ↔ (R.restrict selected).DiscreteOnSupport :=
  ⟨fun h _ _ hr => h hr.1 hr.2.1 hr.2.2, fun h _ _ hl hr rel => h ⟨hl, hr, rel⟩⟩

theorem relativeNormalForm_iff_le (S : PER α) : R.RelativeNormalForm S selected ↔ R.restrict selected ≤ S :=
  ⟨fun h _ _ hr => h hr.1 hr.2.1 hr.2.2, fun h _ _ hl hr rel => h ⟨hl, hr, rel⟩⟩

theorem relativeNormalForm_equality : R.RelativeNormalForm (equality α) selected ↔ R.NormalForm selected :=
  Iff.rfl

theorem Canonical.supportedNormalForm (C : R.Canonical) : R.SupportedNormalForm C.selected :=
  Proofs.Formats.PER.NormalForm.normal C

theorem Canonical.covers (C : R.Canonical) : R.Covers C.selected :=
  fun x hx => (C.representative x hx).exists

def Canonical.ofNormalForm (h : R.SupportedNormalForm selected) (covers : R.Covers selected) : R.Canonical :=
  Proofs.Formats.PER.NormalForm.canonical h covers

/-- Canonicality is coverage, support inclusion and discreteness of the restricted PER. -/
theorem canonical_iff_discrete : (∃ C : R.Canonical, C.selected = selected) ↔
    (∀ ⦃x⦄, selected x → R.Dom x) ∧ R.Covers selected ∧ (R.restrict selected).DiscreteOnSupport := by
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨C.supportedNormalForm.1, C.covers, normalForm_iff_discrete.mp C.supportedNormalForm.2⟩
  · exact fun h => ⟨Canonical.ofNormalForm ⟨h.1, normalForm_iff_discrete.mpr h.2.2⟩ h.2.1, rfl⟩

end Silmaril.Formats.PER
