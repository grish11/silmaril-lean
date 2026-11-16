module

public import Silmaril.Logic.PDL.Mu.Defs

@[expose] public section
namespace Silmaril.Logic.PDL

/-- The star translation computes finite relational paths to the continuation. -/
theorem mu_star_correct {S : Signature} (M : Model S) {n : Nat}
    (c : ModalMu.Formula S n) (body : ModalMu.Formula S (n + 1))
    (ρ : ModalMu.Env M.World n) (r : M.World → M.World → Prop)
    (hbody : ∀ X w, w ∈ body.denote M (ModalMu.extend ρ X) ↔ ∃ v, r w v ∧ v ∈ X)
    (w : M.World) :
    w ∈ (ModalMu.Formula.mu (.disj c.shift body)).denote M ρ ↔
      ∃ v, Relation.ReflTransGen r w v ∧ v ∈ c.denote M ρ := by
  constructor
  · show w ∈ (ModalMu.Formula.mu (.disj c.shift body)).denote M ρ →
      ∃ v, Relation.ReflTransGen r w v ∧ v ∈ c.denote M ρ
    apply ModalMu.Formula.mu_le M _ ρ {u | ∃ v, Relation.ReflTransGen r u v ∧ v ∈ c.denote M ρ}
    intro u hu
    change u ∈ c.shift.denote M (ModalMu.extend ρ _) ∨
      u ∈ body.denote M (ModalMu.extend ρ _) at hu
    have hu' : u ∈ c.denote M ρ ∨ u ∈ body.denote M
        (ModalMu.extend ρ {u | ∃ v, Relation.ReflTransGen r u v ∧ v ∈ c.denote M ρ}) := by
      simpa only [ModalMu.Formula.denote_shift] using hu
    rcases hu' with hc | hb
    · exact ⟨u, .refl, hc⟩
    · obtain ⟨v, huv, t, hvt, ht⟩ := (hbody _ u).mp hb
      exact ⟨t, Relation.ReflTransGen.head huv hvt, ht⟩
  · show (∃ v, Relation.ReflTransGen r w v ∧ v ∈ c.denote M ρ) →
      w ∈ (ModalMu.Formula.mu (.disj c.shift body)).denote M ρ
    rintro ⟨v, hpath, hv⟩
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl =>
        rw [ModalMu.Formula.mu_unfold]
        change v ∈ c.shift.denote M (ModalMu.extend ρ _) ∨ _
        rw [ModalMu.Formula.denote_shift]
        exact Or.inl hv
    | @head u t hut _ ih =>
        rw [ModalMu.Formula.mu_unfold]
        apply Or.inr
        exact (hbody _ u).mpr ⟨t, hut, ih⟩

end Silmaril.Logic.PDL
