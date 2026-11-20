module

public import Mathlib.Logic.Equiv.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Defs

public section

namespace Silmaril.Proofs.Wasm.Validation.Intrinsic

/-- A sound, surjective erasure becomes bijective after identifying exactly equal erasures. -/
noncomputable def erasureEquiv {α β : Type} {valid : β → Prop} (erase : α → β)
    (sound : ∀ term, valid (erase term)) (complete : ∀ {raw}, valid raw → ∃ term, erase term = raw) :
    Quot (fun left right => erase left = erase right) ≃ Subtype valid where
  toFun := Quot.lift (fun term => ⟨erase term, sound term⟩) (fun _ _ eq => Subtype.ext eq)
  invFun := fun raw => Quot.mk _ (Classical.choose (complete raw.property))
  left_inv := by
    intro term
    induction term using Quot.ind with
    | mk term => exact Quot.sound (Classical.choose_spec (complete (sound term)))
  right_inv := fun raw => Subtype.ext (Classical.choose_spec (complete raw.property))

end Silmaril.Proofs.Wasm.Validation.Intrinsic
