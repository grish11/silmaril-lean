module

public import Silmaril.Courses.Cambridge.L2.Substitution

/-! # Closing a lambda body and then taking a beta step -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.PureDenotation

def extendSubst (argument : Expr) (σ : Nat → Expr) : Nat → Expr
  | 0 => argument
  | i + 1 => σ i

private theorem lift_comp (σ : Nat → Expr) (ρ : Nat → Nat) :
    Expr.liftSubst (σ ∘ ρ) = Expr.liftSubst σ ∘ DeBruijn.lift ρ := by
  funext i
  cases i <;> rfl

private theorem subst_rename (e : Expr) (ρ : Nat → Nat) (σ : Nat → Expr) :
    (e.rename ρ).subst σ = e.subst (σ ∘ ρ) := by
  induction e generalizing ρ σ <;>
    simp_all only [Expr.rename, Expr.subst, lift_comp, DeBruijn.liftN, Function.comp_apply]

private theorem rename_lift (σ : Nat → Expr) (ρ : Nat → Nat) :
    (fun i => (Expr.liftSubst σ i).rename (DeBruijn.lift ρ)) =
      Expr.liftSubst (fun i => (σ i).rename ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ =>
    simp only [Expr.liftSubst, Expr.rename_comp]
    rfl

private theorem rename_subst (e : Expr) (σ : Nat → Expr) (ρ : Nat → Nat) :
    (e.subst σ).rename ρ = e.subst (fun i => (σ i).rename ρ) := by
  induction e generalizing σ ρ <;>
    simp_all only [Expr.rename, Expr.subst, DeBruijn.liftN, rename_lift]

private theorem subst_lift (σ τ : Nat → Expr) :
    (fun i => (Expr.liftSubst σ i).subst (Expr.liftSubst τ)) =
      Expr.liftSubst (fun i => (σ i).subst τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ =>
    simp only [Expr.liftSubst, subst_rename, rename_subst]
    rfl

private theorem subst_comp (e : Expr) (σ τ : Nat → Expr) :
    (e.subst σ).subst τ = e.subst (fun i => (σ i).subst τ) := by
  induction e generalizing σ τ <;>
    simp_all only [Expr.subst, subst_lift]

/-- Applying a closed-over body is equivalent to extending its saved substitution. -/
theorem beta_after_subst (body argument : Expr) (σ : Nat → Expr) :
    (body.subst (Expr.liftSubst σ)).beta argument = body.subst (extendSubst argument σ) := by
  rw [Expr.beta, subst_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ =>
    rw [Expr.liftSubst, subst_rename]
    exact Expr.subst_id _

end Silmaril.Courses.Cambridge.L2.PureDenotation
