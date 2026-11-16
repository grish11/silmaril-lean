module

public import Silmaril.Logic.Institution.SetSentences.Defs
public import Silmaril.Logic.Institution.Faithful

@[expose] public section
namespace Silmaril.Logic.Institution.SetSentences
open CategoryTheory Silmaril.Logic.Institution
universe w m₁ m₂

theorem satisfies_iff (R : Room.{w,m₁,m₂}) (M : R.Mod) (Γ : Set R.Sen) :
    (room R).Sat M Γ ↔ M ∈ R.modelsOf Γ := Iff.rfl

theorem satisfies_empty (R : Room.{w,m₁,m₂}) (M : R.Mod) :
    (room R).Sat M (∅ : Set R.Sen) := by
  intro φ hφ
  exact (Set.notMem_empty φ hφ).elim

theorem satisfies_union (R : Room.{w,m₁,m₂}) (M : R.Mod) (Γ Δ : Set R.Sen) :
    (room R).Sat M (Γ ∪ Δ : Set R.Sen) ↔ (room R).Sat M Γ ∧ (room R).Sat M Δ := by
  constructor
  · intro h
    exact ⟨fun φ hφ => h φ (Or.inl hφ), fun φ hφ => h φ (Or.inr hφ)⟩
  · rintro ⟨hΓ, hΔ⟩ φ (hφ | hφ)
    · exact hΓ φ hφ
    · exact hΔ φ hφ

theorem satisfiable_iff (R : Room.{w,m₁,m₂}) (Γ : Set R.Sen) :
    (∃ M, (room R).Sat M Γ) ↔ ∃ M, ∀ φ ∈ Γ, R.Sat M φ := Iff.rfl

theorem singleton_satisfaction (R : Room.{w,m₁,m₂}) (M : R.Mod) (φ : R.Sen) :
    (room R).Sat M ((singletonCorridor R).sen φ) ↔ R.Sat M φ :=
  (singletonCorridor R).sat M φ

/-- Exact expansion uses the very same object, not a chosen isomorphic copy. -/
theorem singleton_modelExpansive (R : Room.{w,m₁,m₂}) :
    Corridor.ModelExpansive (singletonCorridor R) := fun M => ⟨M, rfl⟩

theorem singleton_isoExpansive (R : Room.{w,m₁,m₂}) :
    Corridor.IsoExpansive (singletonCorridor R) :=
  fun M => ⟨M, ⟨Iso.refl M⟩⟩

/-- Collapsed sentence maps still preserve the full conjunction: distinct
source sentences may share one image; no injectivity assumption is used. -/
theorem collapsed_pair {R S : Room.{w,m₁,m₂}} (c : R ⟶ S)
    (φ ψ : R.Sen) (h : c.sen φ = c.sen ψ) :
    (corridor c).sen ({φ, ψ} : Set R.Sen) = ({c.sen φ} : Set S.Sen) := by
  change c.sen '' ({φ, ψ} : Set R.Sen) = {c.sen φ}
  rw [Set.image_pair, h]
  ext q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self]

end Silmaril.Logic.Institution.SetSentences
