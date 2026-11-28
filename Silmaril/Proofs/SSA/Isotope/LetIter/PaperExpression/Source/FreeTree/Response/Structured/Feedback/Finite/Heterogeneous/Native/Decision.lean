module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Thms

public section

open Silmaril.Isotope Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Proofs

variable {Φ : Type} {c : Code} {a : Expr Φ} {Leaf : Expr Φ → Type}

theorem closed_subst (v : Closed c a) (σ : Nat → Expr Φ) : a.subst σ = a := by
  induction v generalizing σ with
  | literal c v => exact literal_subst c v σ
  | letId _ ih => simp only [Expr.subst, ih, Expr.liftSubst]
  | letInl _ ih => simp only [Expr.subst, ih, Expr.liftSubst]
  | letInr _ ih => simp only [Expr.subst, ih, Expr.liftSubst]

theorem decision_subst (d : Decision Leaf c a) (closed : ∀ {a}, Leaf a → ∀ σ, a.subst σ = a)
    (σ : Nat → Expr Φ) (hσ : σ 0 = .var 0) : a.subst σ = a := by
  induction d generalizing σ with
  | leaf h => exact closed h σ
  | copy _ ih => simp only [Expr.subst, hσ, ih (Expr.liftSubst σ) rfl]
  | split _ _ il ir =>
    simp only [Expr.subst, hσ, il (Expr.liftSubst σ) rfl, ir (Expr.liftSubst σ) rfl]

variable {ε : Type} [HasTy Φ (Ty Unit)] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx (Ty Unit) ε} {e : ε} {A : Ty Unit}

local notation "slot[" c "]" => (Code.ty c, (⊥ : ε))
local notation "Δ₀" => ([] : EffectCtx (Ty Unit) ε)

theorem closed_wf (v : Closed c a) : Wf Γ a c.ty e := by
  induction v generalizing Γ with
  | literal c v => exact literal_wf c v
  | letId _ ih => exact .let₁ ih (.var 0 bot_le)
  | letInl _ ih => exact .let₁ ih (.inl (.var 0 bot_le))
  | letInr _ ih => exact .let₁ ih (.inr (.var 0 bot_le))

theorem closed_eqv (v : Closed c a) : Eqv Γ c.ty e a (c.literal v.read) := by
  induction v with
  | literal c v => exact .refl (literal_wf c v)
  | letId v ih =>
    exact (Eqv.step (.let1_beta (closed_wf v) (.var 0 bot_le))).trans ih
  | letInl v ih =>
    exact (Eqv.step (.let1_beta (closed_wf v) (.inl (.var 0 bot_le)))).trans (.inl ih)
  | letInr v ih =>
    exact (Eqv.step (.let1_beta (closed_wf v) (.inr (.var 0 bot_le)))).trans (.inr ih)

theorem decision_wf (d : Decision Leaf c a)
    (leaves : ∀ {Δ : EffectCtx (Ty Unit) ε} {a}, Leaf a → Wf Δ a A e) :
    Wf (slot[c] :: Γ) a A e := by
  induction d generalizing Γ with
  | leaf h => exact leaves h
  | copy _ ih => exact .let₁ (.var 0 bot_le) ih
  | split _ _ il ir => exact .case (.var 0 bot_le) il ir

private theorem readback (d : Decision Leaf c a)
    (closed : ∀ {a}, Leaf a → ∀ σ, a.subst σ = a)
    (leaves : ∀ {Δ : EffectCtx (Ty Unit) ε} {a}, Leaf a → Wf Δ a A e)
    (v : c.Value) : Eqv Δ₀ A e (a.subst (c.literal v).subst0) (d.read v).1 := by
  induction d with
  | leaf h =>
    rw [closed h]
    exact .refl (leaves h)
  | @copy k a d ih =>
    simp only [Expr.subst, Expr.subst0, Decision.read]
    rw [decision_subst d closed (Expr.liftSubst (k.literal v).subst0) rfl]
    exact (Eqv.step (.let1_beta (literal_wf k v) (decision_wf d leaves))).trans (ih v)
  | @split l r a b left right il ir =>
    simp only [Expr.subst, Expr.subst0]
    rw [decision_subst left closed (Expr.liftSubst ((Code.sum l r).literal v).subst0) rfl,
      decision_subst right closed (Expr.liftSubst ((Code.sum l r).literal v).subst0) rfl]
    have hl := decision_wf (Γ := Δ₀) left leaves
    have hr := decision_wf (Γ := Δ₀) right leaves
    cases v with
    | inl v =>
      have hv : Wf Δ₀ (l.literal v : Expr Φ) l.ty (⊥ : ε) := literal_wf l v
      have beta := KnownTag.case_eqv (.inl (literal_wf l v)) hl hr
      exact beta.trans ((Eqv.step (.let1_beta hv hl)).trans (il v))
    | inr v =>
      have hv : Wf Δ₀ (r.literal v : Expr Φ) r.ty (⊥ : ε) := literal_wf r v
      have beta := KnownTag.case_eqv (.inr (literal_wf r v)) hl hr
      exact beta.trans ((Eqv.step (.let1_beta hv hr)).trans (ir v))

/-- Specialize the actual decision to each input before reassembling it
with the existing exhaustive constructor-code source equation. -/
theorem decision_eqv (d : Decision Leaf c a)
    (closed : ∀ {a}, Leaf a → ∀ σ, a.subst σ = a)
    (leaves : ∀ {Δ : EffectCtx (Ty Unit) ε} {a}, Leaf a → Wf Δ a A e)
    (rows : c.Value → Expr Φ) (rowClosed : ∀ v σ, (rows v).subst σ = rows v)
    (rowTyped : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) A e)
    (normalize : ∀ v, Eqv Δ₀ A e (d.read v).1 (rows v)) :
    Eqv [slot[c]] A e a (c.dispatch rows (.var 0)) := by
  refine eqv_by_codes c (decision_wf d leaves) (dispatch_wf c rowTyped (.var 0 bot_le)) (fun v => ?_)
  rw [dispatch_subst c rowClosed]
  exact (readback d closed leaves v).trans ((normalize v).trans (dispatch_beta c v rowClosed rowTyped).symm)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Proofs
