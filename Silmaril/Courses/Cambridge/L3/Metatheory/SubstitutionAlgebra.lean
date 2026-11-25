module

public import Silmaril.Courses.Cambridge.L3.Store

/-! # L3 de Bruijn substitution laws for lexical evaluation -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

theorem Expr.rename_comp (e : Expr) (ρ τ : Nat → Nat) :
    (e.rename ρ).rename τ = e.rename (τ ∘ ρ) := by
  induction e generalizing ρ τ <;>
    simp_all only [Expr.rename, DeBruijn.lift_comp, DeBruijn.liftN_comp, Function.comp_apply]

private theorem lift_bvar : Expr.liftSubst Expr.bvar = Expr.bvar := by
  funext i
  cases i <;> rfl

theorem Expr.subst_id (e : Expr) : e.subst Expr.bvar = e := by
  induction e <;> simp_all only [Expr.subst, lift_bvar]

private theorem lift_comp (σ : Nat → Expr) (ρ : Nat → Nat) :
    Expr.liftSubst (σ ∘ ρ) = Expr.liftSubst σ ∘ DeBruijn.lift ρ := by
  funext i
  cases i <;> rfl

theorem Expr.subst_rename (e : Expr) (ρ : Nat → Nat) (σ : Nat → Expr) :
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

theorem Expr.rename_subst (e : Expr) (σ : Nat → Expr) (ρ : Nat → Nat) :
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
      simp only [Expr.liftSubst, Expr.subst_rename, Expr.rename_subst]
      rfl

theorem Expr.subst_comp (e : Expr) (σ τ : Nat → Expr) :
    (e.subst σ).subst τ = e.subst (fun i => (σ i).subst τ) := by
  induction e generalizing σ τ <;> simp_all only [Expr.subst, subst_lift]

theorem IsValue.rename {e : Expr} (ready : IsValue e) (ρ : Nat → Nat) :
    IsValue (e.rename ρ) := by
  induction ready with
  | int => exact .int _
  | bool => exact .bool _
  | skip => exact .skip
  | loc => exact .loc _
  | lam => exact .lam _ _
  | pair _ _ hl hr => exact .pair hl hr
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | record _ ih => exact .record ih

theorem IsValue.subst {e : Expr} (ready : IsValue e) (σ : Nat → Expr) :
    IsValue (e.subst σ) := by
  induction ready with
  | int => exact .int _
  | bool => exact .bool _
  | skip => exact .skip
  | loc => exact .loc _
  | lam => exact .lam _ _
  | pair _ _ hl hr => exact .pair hl hr
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | record _ ih => exact .record ih

end Silmaril.Courses.Cambridge.L3
