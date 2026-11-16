module

public import Silmaril.Proofs.Logic.PDL.StarTranslation

@[expose] public section
namespace Silmaril.Logic.PDL

 theorem mu_closed_dual {S : Signature} (M : Model S) (p : ModalMu.Formula S 0)
    (w : M.World) : w ∈ p.dual.denote M ModalMu.emptyEnv ↔
      ¬ w ∈ p.denote M ModalMu.emptyEnv := by
  have he : (fun i : Fin 0 => (ModalMu.emptyEnv (W := M.World) i)ᶜ) = ModalMu.emptyEnv :=
    funext fun i => i.elim0
  have hd := p.denote_dual M ModalMu.emptyEnv
  rw [he] at hd
  exact Set.ext_iff.mp hd w

mutual
  /-- Closed PDL formulas and their translated μ formulas agree at every world. -/
  theorem Formula.toMu_correct {S : Signature} (M : Model S) (p : Formula S) (w : M.World) :
      w ∈ p.toMu.denote M ModalMu.emptyEnv ↔ p.Holds M w := by
    classical
    cases p with
    | atom a => rfl
    | bot => rfl
    | neg p => exact (mu_closed_dual M p.toMu w).trans (not_congr (Formula.toMu_correct M p w))
    | conj p q => exact and_congr (Formula.toMu_correct M p w) (Formula.toMu_correct M q w)
    | disj p q => exact or_congr (Formula.toMu_correct M p w) (Formula.toMu_correct M q w)
    | box a p =>
        change w ∈ (a.toMu p.toMu.dual).dual.denote M ModalMu.emptyEnv ↔
          ∀ v, a.Rel M w v → p.Holds M v
        rw [mu_closed_dual, Program.toMu_correct M a p.toMu.dual ModalMu.emptyEnv w]
        simp_rw [mu_closed_dual, Formula.toMu_correct M p]
        simp only [not_exists, not_and, not_not]
    | diamond a p =>
        change w ∈ (a.toMu p.toMu).denote M ModalMu.emptyEnv ↔
          ∃ v, a.Rel M w v ∧ p.Holds M v
        rw [Program.toMu_correct M a p.toMu ModalMu.emptyEnv w]
        exact exists_congr fun v => and_congr Iff.rfl (Formula.toMu_correct M p v)
  termination_by sizeOf p

  /-- The continuation theorem covers all programs, including nested tests and stars,
  in every free-variable environment. -/
  theorem Program.toMu_correct {S : Signature} (M : Model S) (a : Program S)
      {n : Nat} (c : ModalMu.Formula S n) (ρ : ModalMu.Env M.World n) (w : M.World) :
      w ∈ (a.toMu c).denote M ρ ↔ ∃ v, a.Rel M w v ∧ v ∈ c.denote M ρ := by
    cases a with
    | action a => rfl
    | seq a b =>
        change w ∈ (a.toMu (b.toMu c)).denote M ρ ↔
          ∃ v, (∃ u, a.Rel M w u ∧ b.Rel M u v) ∧ v ∈ c.denote M ρ
        rw [Program.toMu_correct M a (b.toMu c) ρ w]
        simp_rw [Program.toMu_correct M b c ρ]
        constructor
        · rintro ⟨u, hu, v, hv, hc⟩
          exact ⟨v, ⟨u, hu, hv⟩, hc⟩
        · rintro ⟨v, ⟨u, hu, hv⟩, hc⟩
          exact ⟨u, hu, v, hv, hc⟩
    | choice a b =>
        change (w ∈ (a.toMu c).denote M ρ ∨ w ∈ (b.toMu c).denote M ρ) ↔
          ∃ v, (a.Rel M w v ∨ b.Rel M w v) ∧ v ∈ c.denote M ρ
        rw [Program.toMu_correct M a c ρ w, Program.toMu_correct M b c ρ w]
        constructor
        · rintro (⟨v, hv, hc⟩ | ⟨v, hv, hc⟩)
          · exact ⟨v, Or.inl hv, hc⟩
          · exact ⟨v, Or.inr hv, hc⟩
        · rintro ⟨v, (hv | hv), hc⟩
          · exact Or.inl ⟨v, hv, hc⟩
          · exact Or.inr ⟨v, hv, hc⟩
    | star a =>
        apply mu_star_correct M c (a.toMu (.var 0)) ρ (a.Rel M)
        intro X u
        exact Program.toMu_correct M a (.var 0) (ModalMu.extend ρ X) u
    | test p =>
        change (w ∈ (p.toMu.closedAt n).denote M ρ ∧ w ∈ c.denote M ρ) ↔
          ∃ v, (w = v ∧ p.Holds M w) ∧ v ∈ c.denote M ρ
        rw [ModalMu.Formula.denote_closedAt, Formula.toMu_correct M p w]
        constructor
        · intro h
          exact ⟨w, ⟨rfl, h.1⟩, h.2⟩
        · rintro ⟨v, ⟨rfl, hp⟩, hc⟩
          exact ⟨hp, hc⟩
  termination_by sizeOf a
end

end Silmaril.Logic.PDL
