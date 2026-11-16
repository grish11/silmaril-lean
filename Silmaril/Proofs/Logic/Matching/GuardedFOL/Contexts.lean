module

public import Silmaril.Logic.Matching.GuardedFOL.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.GuardedFOL

theorem context_eq {S : Type} {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) : Δ = Fin.cases (Δ 0) Γ := by
  funext i
  exact Fin.cases rfl (congrFun h) i

def extend {S : Type} (C : S → Type) {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) (v : ∀ i, C (Γ i)) (x : C (Δ 0)) : ∀ i, C (Δ i) :=
  Eq.rec (motive := fun Θ _ => ∀ i, C (Θ i)) (Fin.cases x v) (context_eq h).symm

theorem context_cast_apply {S : Type} (C : S → Type) {k : Nat} {Γ Δ : Fin k → S}
    (h : Γ = Δ) (v : ∀ i, C (Γ i)) (i : Fin k) :
    HEq ((h ▸ v : ∀ i, C (Δ i)) i) (v i) := by cases h; rfl

theorem extend_zero {S : Type} (C : S → Type) {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) (v : ∀ i, C (Γ i)) (x : C (Δ 0)) : extend C h v x 0 = x := by
  unfold extend
  exact eq_of_heq (context_cast_apply C (context_eq h).symm
    (show (∀ i, C (Fin.cases (Δ 0) Γ i)) from Fin.cases x v) 0)

theorem extend_succ {S : Type} (C : S → Type) {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) (v : ∀ i, C (Γ i)) (x : C (Δ 0)) (i : Fin k) :
    HEq (extend C h v x i.succ) (v i) := by
  unfold extend
  exact context_cast_apply C (context_eq h).symm
    (show (∀ i, C (Fin.cases (Δ 0) Γ i)) from Fin.cases x v) i.succ

theorem forall_extensions {S : Type} (C : S → Type) {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) (v : ∀ i, C (Γ i)) (P : (∀ i, C (Δ i)) → Prop) :
    (∀ x, P (extend C h v x)) ↔ ∀ θ, (∀ i, HEq (θ i.succ) (v i)) → P θ := by
  constructor
  · intro hall θ hθ
    have same : extend C h v (θ 0) = θ := by
      funext i
      cases i using Fin.cases with
      | zero => exact extend_zero C h v (θ 0)
      | succ i => exact eq_of_heq ((extend_succ C h v (θ 0) i).trans (hθ i).symm)
    exact same ▸ hall (θ 0)
  · intro hall x
    exact hall _ (extend_succ C h v x)

private theorem cast_natural {S : Type} {C D : S → Type} (f : ∀ s, C s → D s)
    {k : Nat} {Γ Δ : Fin k → S} (h : Γ = Δ) (v : ∀ i, C (Γ i)) :
    (fun i => f (Δ i) ((h ▸ v : ∀ i, C (Δ i)) i)) =
      (h ▸ (fun i => f (Γ i) (v i)) : ∀ i, D (Δ i)) := by cases h; rfl

theorem extend_natural {S : Type} {C D : S → Type} (f : ∀ s, C s → D s)
    {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S} (h : Δ ∘ Fin.succ = Γ)
    (v : ∀ i, C (Γ i)) (x : C (Δ 0)) :
    (fun i => f (Δ i) (extend C h v x i)) = extend D h (fun i => f (Γ i) (v i)) (f (Δ 0) x) := by
  unfold extend
  rw [cast_natural]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i
end Silmaril.Logic.Matching.GuardedFOL
