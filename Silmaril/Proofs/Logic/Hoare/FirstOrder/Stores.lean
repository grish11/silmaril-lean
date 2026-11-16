module

public import Silmaril.Logic.Hoare.FirstOrder.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Proofs.Logic.Hoare.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Hoare.FirstOrder
variable {A : FOL.Signature} (M : FOL.Structure A)

theorem slot_lt {k} (i : Fin k) : slot i < k := by unfold slot; omega

theorem slot_succ {k} (i : Fin k) : slot i.succ = slot i := by
  unfold slot; simp only [Fin.val_succ]; omega

theorem slot_zero (k : Nat) : slot (0 : Fin (k+1)) = k := by simp [slot]

theorem encodes_unique {k} {Γ : Fin k → A.S} {ρ σ : ∀ i, M.carrier (Γ i)}
    {h : Store M} (hρ : Encodes M Γ ρ h) (hσ : Encodes M Γ σ h) : σ = ρ := by
  funext i
  exact eq_of_heq (Sigma.mk.inj (Option.some.inj ((hσ i).symm.trans (hρ i)))).2

/-- The key invariant permits arbitrary unrelated and stale store contents. -/
theorem update_encodes {k} {Γ : Fin k → A.S} {Δ : Fin (k+1) → A.S}
    (hc : Δ ∘ Fin.succ = Γ) {ρ : ∀ i, M.carrier (Γ i)} {h : Store M}
    (hh : Encodes M Γ ρ h) (θ : ∀ i, M.carrier (Δ i))
    (agree : ∀ i, HEq (θ i.succ) (ρ i)) :
    Encodes M Δ θ (Function.update h k (some ⟨Δ 0, θ 0⟩)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [slot_zero, Function.update_self]
  · rw [slot_succ, Function.update_of_ne (show slot j ≠ k by have := slot_lt j; omega)]
    exact (hh j).trans (congrArg some (Sigma.ext (congrFun hc j) (agree j))).symm

def extend {k} {Γ : Fin k → A.S} {Δ : Fin (k+1) → A.S}
    (hc : Δ ∘ Fin.succ = Γ) (ρ : ∀ i, M.carrier (Γ i)) (x : M.carrier (Δ 0)) :
    ∀ i, M.carrier (Δ i) :=
  Fin.cases x (fun i => (congrArg M.carrier (congrFun hc i).symm) ▸ ρ i)

theorem extend_agree {k} {Γ : Fin k → A.S} {Δ : Fin (k+1) → A.S}
    (hc : Δ ∘ Fin.succ = Γ) (ρ : ∀ i, M.carrier (Γ i)) (x : M.carrier (Δ 0)) (i : Fin k) :
    HEq (extend M hc ρ x i.succ) (ρ i) := by
  simp only [extend, Fin.cases_succ]
  exact cast_heq _ _

end Silmaril.Proofs.Logic.Hoare.FirstOrder
