module

public import Silmaril.Logic.Separation.FirstOrder.Models

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.FirstOrder
open Silmaril.Logic.Institution.Examples
variable {A : FOL.Signature} (M : FOL.Structure A)

theorem slot_lt {k} (i : Fin k) : slot i < k := by unfold slot; omega

theorem slot_succ {k} (i : Fin k) : slot i.succ = slot i := by
  unfold slot; simp only [Fin.val_succ]; omega

theorem slot_zero (k : Nat) : slot (0 : Fin (k+1)) = k := by simp [slot]

theorem store_at {k} (Γ : Fin k → A.S) (ρ : ∀ i, M.carrier (Γ i)) (i : Fin k) :
    store M Γ ρ (slot i) = some ⟨Γ i, ρ i⟩ := by
  unfold store
  rw [dite_eq_left (slot_lt i)]
  have hi : (⟨k - 1 - slot i, by have := slot_lt i; unfold slot at *; omega⟩ : Fin k) = i := by
    apply Fin.ext; unfold slot; simp only; omega
  exact congrArg (fun j => some (⟨Γ j, ρ j⟩ : Value M)) hi

theorem store_out {k} (Γ : Fin k → A.S) (ρ : ∀ i, M.carrier (Γ i)) {n : Nat}
    (hn : k ≤ n) : store M Γ ρ n = none := by simp [store, Nat.not_lt.mpr hn]

/-- The complete store has exactly the initial segment as its ownership domain. -/
theorem store_domain {k} (Γ : Fin k → A.S) (ρ : ∀ i, M.carrier (Γ i)) (n : Nat) :
    store M Γ ρ n ≠ none ↔ n < k := by
  by_cases hn : n < k <;> simp [store, hn]

theorem store_encodes {k} (Γ : Fin k → A.S) (ρ : ∀ i, M.carrier (Γ i)) :
    Encodes M Γ ρ (store M Γ ρ) := store_at M Γ ρ

theorem encodes_unique {k} (Γ : Fin k → A.S) (ρ σ : ∀ i, M.carrier (Γ i))
    (hh : Encodes M Γ σ (store M Γ ρ)) : σ = ρ := by
  funext i
  have he := (hh i).symm.trans (store_at M Γ ρ i)
  exact eq_of_heq (Sigma.mk.inj (Option.some.inj he)).2

theorem store_empty (Γ : Fin 0 → A.S) (ρ : ∀ i, M.carrier (Γ i)) :
    store M Γ ρ = empty := by funext n; exact store_out M Γ ρ (Nat.zero_le n)

/-- Public binder agreement yields exact native disjoint extension, with no junk. -/
theorem store_join {k} {Γ : Fin k → A.S} {Δ : Fin (k+1) → A.S}
    (hc : Δ ∘ Fin.succ = Γ) (ρ : ∀ i, M.carrier (Γ i))
    (θ : ∀ i, M.carrier (Δ i)) (agree : ∀ i, HEq (θ i.succ) (ρ i)) :
    Join (store M Γ ρ) (singleton k ⟨Δ 0, θ 0⟩) (store M Δ θ) := by
  intro n
  by_cases hn : n < k
  · let i : Fin k := ⟨k-1-n, by omega⟩
    have hi : slot i = n := by unfold slot; dsimp [i]; omega
    have hv : (⟨Δ i.succ, θ i.succ⟩ : Value M) = ⟨Γ i, ρ i⟩ :=
      Sigma.ext (congrFun hc i) (agree i)
    have old := store_at M Γ ρ i
    have new := store_at M Δ θ i.succ
    rw [slot_succ, hi] at new
    rw [hi] at old
    exact Or.inr ⟨by simp [singleton, show n ≠ k by omega], by rw [old, new, hv]⟩
  · by_cases he : n = k
    · subst n
      exact Or.inl ⟨store_out M Γ ρ (Nat.le_refl k), by
        simpa only [slot_zero, singleton, ite_true] using (store_at M Δ θ 0).symm⟩
    · exact Or.inl ⟨store_out M Γ ρ (by omega), by
        rw [store_out M Δ θ (by omega)]; simp [singleton, he]⟩

theorem extend_agree {k} {Γ : Fin k → A.S} {Δ : Fin (k+1) → A.S}
    (hc : Δ ∘ Fin.succ = Γ) (ρ : ∀ i, M.carrier (Γ i)) (x : M.carrier (Δ 0)) (i : Fin k) :
    HEq (extend M hc ρ x i.succ) (ρ i) := by
  simp only [extend, Fin.cases_succ]
  exact cast_heq _ _

/-- Every compatible fresh cell produces exactly the corresponding extended store. -/
theorem extension_exact {k} {Γ : Fin k → A.S} {Δ : Fin (k+1) → A.S}
    (hc : Δ ∘ Fin.succ = Γ) (ρ : ∀ i, M.carrier (Γ i))
    {a b : ModelStore M} (hj : Join (store M Γ ρ) a b)
    (ha : a ∈ atom M (.cell k (Δ 0))) :
    ∃ θ : ∀ i, M.carrier (Δ i), (∀ i, HEq (θ i.succ) (ρ i)) ∧ b = store M Δ θ := by
  obtain ⟨x,rfl⟩ := ha
  refine ⟨extend M hc ρ x, extend_agree M hc ρ x, ?_⟩
  apply (resource (Value M)).functional hj
  exact store_join M hc ρ (extend M hc ρ x) (extend_agree M hc ρ x)

end Silmaril.Logic.Separation.FirstOrder
