module

public import Silmaril.Proofs.Logic.Hoare.FirstOrder.Stores

@[expose] public section
noncomputable section
namespace Silmaril.Proofs.Logic.Hoare.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Hoare.FirstOrder
variable {A : FOL.Signature}

/-- Open correctness holds in every store encoding the context, not just exact stores. -/
theorem compile_correct (M : FOL.Structure A) {k} {Γ : Fin k → A.S}
    (φ : FOL.Formula A Γ) (ρ : ∀ i, M.carrier (Γ i)) (h : Store M)
    (hh : Encodes M Γ ρ h) :
    (compile φ).Holds (native M) h ↔ φ.Holds M ρ := by
  induction φ generalizing h with
  | eq t u =>
      change (∃ σ, Encodes M _ σ h ∧ _) ↔ _
      constructor
      · rintro ⟨σ,hσ,he⟩
        exact (encodes_unique M hh hσ) ▸ he
      · intro he
        exact ⟨ρ,hh,he⟩
  | rel r args =>
      change (∃ σ, Encodes M _ σ h ∧ _) ↔ _
      constructor
      · rintro ⟨σ,hσ,he⟩
        exact (encodes_unique M hh hσ) ▸ he
      · intro he
        exact ⟨ρ,hh,he⟩
  | tt => exact Iff.intro (fun _ => True.intro) (fun _ => not_false)
  | not φ ih => exact not_congr (ih ρ h hh)
  | and φ ψ hp hq => exact and_congr (hp ρ h hh) (hq ρ h hh)
  | all hc φ ih =>
      change (∀ h', havoc M _ h h' → (compile φ).Holds (native M) h') ↔ _
      constructor
      · intro hb θ agree
        exact (ih θ _ (update_encodes M hc hh θ agree)).1
          (hb _ ⟨θ 0,rfl⟩)
      · intro hall h' step
        obtain ⟨x,rfl⟩ := step
        let θ := extend M hc ρ x
        have agree : ∀ i, HEq (θ i.succ) (ρ i) := extend_agree M hc ρ x
        exact (ih θ _ (update_encodes M hc hh θ agree)).2 (hall θ agree)

theorem closed_correct (M : FOL.Structure A) (φ : FOL.Sentence A) (h : Store M) :
    (compile φ.formula).Holds (native M) h ↔ φ.Holds M :=
  compile_correct M φ.formula (fun i => i.elim0) h (fun i => i.elim0)

theorem sentence_correct (M : FOL.Structure A) (φ : FOL.Sentence A) :
    (sentence φ).Satisfies (Command A.S) (native M) ↔ φ.Holds M := by
  constructor
  · intro hs
    exact (closed_correct M φ (empty M)).1
      (hs (empty M) not_false (empty M) ⟨rfl,not_false⟩)
  · intro hf h _ h' step
    exact (closed_correct M φ h').2 hf

end Silmaril.Proofs.Logic.Hoare.FirstOrder
