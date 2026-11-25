module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Equations

/-! # Substitution for source typing and equations -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Expr

variable {Φ : Type v}

/-- Renaming distributes over a substitution. -/
theorem wk_subst (a : Expr Φ) (σ : Nat → Expr Φ) (ρ : Nat → Nat) :
    (a.subst σ).wk ρ = a.subst (fun i => (σ i).wk ρ) :=
  Source.Proofs.wk_subst a σ ρ

/-- Substitution after renaming composes the maps on variables. -/
theorem subst_wk (a : Expr Φ) (σ : Nat → Expr Φ) (ρ : Nat → Nat) :
    (a.wk ρ).subst σ = a.subst (σ ∘ ρ) :=
  Source.Proofs.subst_wk a σ ρ

/-- View a renaming as a substitution of variables. -/
theorem wk_eq_subst (a : Expr Φ) (ρ : Nat → Nat) :
    a.wk ρ = a.subst (Expr.var ∘ ρ) := by
  rw [← Source.Proofs.subst_wk, Source.Proofs.subst_var]

theorem subst_var (a : Expr Φ) : a.subst Expr.var = a := Source.Proofs.subst_var a

end Silmaril.Isotope.LetIter.PaperExpression.Expr

namespace Silmaril.Isotope.LetIter.PaperExpression

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ Δ : EffectCtx τ ε} {a b : Expr Φ} {A : τ} {e : ε} {σ θ : Nat → Expr Φ}

/-- A typed substitution preserves the original typing bound. -/
theorem Wf.subst_typed (ha : Wf Δ a A e)
    (hσ : ∀ i : Fin Δ.length, Wf Γ (σ i.val) (Δ.get i).1 (Δ.get i).2) :
    Wf Γ (a.subst σ) A e :=
  Source.Proofs.wf_subst ha hσ

/-- Pointwise equal substitutions give equal expressions at the same bound. -/
theorem Wf.subst_congr (ha : Wf Δ a A e)
    (hσ : ∀ i : Fin Δ.length, Source.Eqv Γ (Δ.get i).1 (Δ.get i).2 (σ i.val) (θ i.val)) :
    Source.Eqv Γ A e (a.subst σ) (a.subst θ) :=
  Source.Proofs.eqv_subst_congr ha hσ

namespace Source

/-- Both endpoints of a source equation are typed at its bound. -/
theorem Eqv.endpoints_wf (h : Eqv Γ A e a b) : Wf Γ a A e ∧ Wf Γ b A e :=
  Proofs.eqv_typed h

/-- Source equality is preserved by substitutions typed at each slot's effect. -/
theorem Eqv.subst_typed (h : Eqv Δ A e a b)
    (hσ : ∀ i : Fin Δ.length, Wf Γ (σ i.val) (Δ.get i).1 (Δ.get i).2) :
    Eqv Γ A e (a.subst σ) (b.subst σ) :=
  Proofs.eqv_subst h hσ

/-- Source equality is preserved by renaming into variables of the same types and bounds. -/
theorem Eqv.wk_typed (h : Eqv Δ A e a b) {ρ : Nat → Nat}
    (hρ : ∀ i : Fin Δ.length, Wf Γ (Expr.var (ρ i.val) : Expr Φ) (Δ.get i).1 (Δ.get i).2) :
    Eqv Γ A e (a.wk ρ) (b.wk ρ) := by
  simpa only [← Proofs.subst_wk, Expr.subst_var] using h.subst_typed (σ := Expr.var ∘ ρ) hρ

/-- A bottom-annotated empty slot equates all endpoints typed at the same bound. -/
theorem eqv_of_empty_slot (i : Fin Γ.length) (ht : (Γ.get i).1 = empty)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a A e) (hb : Wf Γ b A e) :
    Eqv Γ A e a b :=
  .step (.initial ⟨i, ht.symm ▸ InitialType.empty, he⟩ ha hb)

end Source

end Silmaril.Isotope.LetIter.PaperExpression
