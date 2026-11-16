module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution

/-- Stage-bounded source proof trees are valid in each admitted actual interpretation. -/
theorem proof_sound {stage capacity : Stage} {H : Set ScopedTyping} {q : ScopedTyping}
    (d : Proof stage H q) (hCap : stage ≤ capacity)
    (hH : ∀ r ∈ H, CapacityValid capacity r) : CapacityValid capacity q := by
  cases capacity with
  | none => exact d.val.realizes hH
  | some cap => exact d.val.realizesAt (WithTop.coe_le_coe.mp (d.property.trans hCap)) hH

/-- Every stage's original full-rule consequence is sound in its actual models. -/
theorem logic_sound (stage : Stage) : (logic stage).Sound := by
  intro S H q h T hT
  rcases h with ⟨d⟩
  apply proof_sound d T.as.property
  rintro r ⟨s, hs, rfl⟩
  exact hT s hs

/-- Identity stage enlargement is exactly the institution identity. -/
theorem inclusion_refl (stage : Stage) :
    inclusion (le_refl stage) = Inst.CoHom.id (bundled stage) := by
  rfl

/-- Composing inclusions retains the same scoped judgments and actual interpretations. -/
theorem inclusion_comp {stage more most : Stage} (h : stage ≤ more) (k : more ≤ most) :
    inclusion (h.trans k) = Inst.CoHom.comp (inclusion h) (inclusion k) := rfl

/-- No actual finite or full interpretation validates the closed Empty sentence. -/
theorem empty_not_valid (capacity : Stage) :
    ¬ CapacityValid capacity (⟨0, .nil, .zero, .empty⟩ : ScopedTyping) := by
  cases capacity with
  | none =>
    intro h
    rcases h Fin.elim0 trivial with ⟨i, X, hX, ht⟩
    exact hX.no_empty_realizer _ ht
  | some cap =>
    intro h
    exact RawRealizability.no_empty_at .zero Fin.elim0 (h Fin.elim0 trivial)

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution
