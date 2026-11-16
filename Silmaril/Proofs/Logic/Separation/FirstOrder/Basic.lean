module

public import Silmaril.Logic.Separation.FirstOrder.Stores

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.FirstOrder
open Silmaril.Logic.Institution.Examples

variable {A : FOL.Signature}

/-- Exact open semantics on complete well-typed finite stores. -/
theorem compile_correct (M : FOL.Structure A) {k} {Γ : Fin k → A.S}
    (φ : FOL.Formula A Γ) (ρ : ∀ i, M.carrier (Γ i)) :
    store M Γ ρ ∈ (compile φ).denote (native M) ↔ φ.Holds M ρ := by
  induction φ with
  | eq t u =>
      change (∃ σ, Encodes M _ σ (store M _ ρ) ∧ _) ↔ _
      constructor
      · rintro ⟨σ,hh,he⟩
        have hs : σ = ρ := encodes_unique M _ ρ σ hh
        exact hs ▸ he
      · intro he
        exact ⟨ρ,store_encodes M _ ρ,he⟩
  | rel r args =>
      change (∃ σ, Encodes M _ σ (store M _ ρ) ∧ _) ↔ _
      constructor
      · rintro ⟨σ,hh,he⟩
        have hs : σ = ρ := encodes_unique M _ ρ σ hh
        exact hs ▸ he
      · intro he
        exact ⟨ρ,store_encodes M _ ρ,he⟩
  | tt =>
      simp [compile, truth, Assertion.denote, FOL.Formula.Holds]
  | not φ ih => exact not_congr (ih ρ)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ ρ) (ihψ ρ)
  | all hc φ ih =>
      change (∀ a b, Join (store M _ ρ) a b → a ∈ atom M (.cell _ _) →
        b ∈ (compile φ).denote (native M)) ↔ _
      constructor
      · intro hw θ agree
        apply (ih θ).1
        exact hw _ _ (store_join M hc ρ θ agree) ⟨θ 0,rfl⟩
      · intro h a b hj ha
        obtain ⟨θ,agree,rfl⟩ := extension_exact M hc ρ hj ha
        exact (ih θ).2 (h θ agree)

theorem sentence_correct (M : FOL.Structure A) (φ : FOL.Sentence A) :
    (sentence φ).Satisfies (native M) ↔ φ.Holds M := by
  change (({empty} : Set (ModelStore M)) ⊆ (compile φ.formula).denote (native M)) ↔ _
  rw [Set.singleton_subset_iff]
  have h := compile_correct M φ.formula (fun i => i.elim0)
  rw [store_empty] at h
  exact h

end Silmaril.Logic.Separation.FirstOrder
