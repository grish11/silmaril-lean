module
public import Silmaril.Formats.PER.NormalForm.Defs

public section
namespace Silmaril.Proofs.Formats.PER.NormalForm
open Silmaril.Formats Silmaril.Formats.PER
variable {α : Type} {R : PER α} {selected : α → Prop}

@[expose] def canonical (supported : R.SupportedNormalForm selected) (covers : R.Covers selected) : R.Canonical where
  selected := selected
  supported _ hx := supported.1 hx
  representative x hx := by
    obtain ⟨y, hy, rel⟩ := covers x hx
    exact ⟨y, ⟨hy, rel⟩, fun z hz => supported.2 hz.1 hy (R.laws.trans (R.laws.symm hz.2) rel)⟩

theorem normal (C : R.Canonical) : R.SupportedNormalForm C.selected :=
  ⟨fun _ hx => C.supported _ hx, fun _ _ hx hy h => (C.rel_iff _ _).mp ⟨hx, hy, h⟩ |>.2⟩

end Silmaril.Proofs.Formats.PER.NormalForm
