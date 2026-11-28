module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs

/-! # The singleton-return instance of the printed region let₁-case equation -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase

open Paper.RetainedLet (returnOnce)
open Silmaril.DeBruijn (lift)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Both copies of the continuation refer to the selected result at zero.
Their original captures skip the arm's payload binder. -/
def distributed (e a b : Tm Φ) (k : Region Φ) : Region Φ :=
  .case e (.let₁ a (k.renameVars (lift Nat.succ))) (.let₁ b (k.renameVars (lift Nat.succ)))

/-- The singleton instance of Figure 18's let₁-case rule, also present as
the case arm of the acyclic `SumBind.Continuation.ReturnStep` seed.
This standalone seed admits precisely this instance. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | split {Γ : VCtx τ} {A B D : τ} {e a b : Tm Φ}
      (he : Tm.HasType Γ e (coprod A B)) (ha : Tm.HasType (A :: Γ) a D)
      (hb : Tm.HasType (B :: Γ) b D) :
      Step Γ (returnOnce (.case e a b)) (.case e (returnOnce a) (returnOnce b)) [D]

abbrev Eqv := Paper.Extension.Eqv (Step (τ := τ) (Φ := Φ))

theorem Step.valueBranches {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Step Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | split he ha hb =>
    exact ⟨UnaryReturn.returnOnce_valueBranches (.case he ha hb),
      .case he (UnaryReturn.returnOnce_valueBranches ha) (UnaryReturn.returnOnce_valueBranches hb)⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase
