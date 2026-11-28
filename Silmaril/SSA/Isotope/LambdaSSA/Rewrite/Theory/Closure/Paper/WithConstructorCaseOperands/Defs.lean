module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs

/-! # Opt-in constructor beta at a typed primitive operand -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorCaseOperands

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Select the arm of a known constructor and substitute its actual payload.
The payload must be a value. Both arms have ordinary term typing and may
contain effects. -/
inductive OperandBeta : VCtx τ → Tm Φ → Tm Φ → τ → Prop where
  | left {Γ : VCtx τ} {a l r : Tm Φ} {A B D : τ}
      (ha : Tm.BranchValue Γ a A)
      (hl : Tm.HasType (A :: Γ) l D) (hr : Tm.HasType (B :: Γ) r D) :
      OperandBeta Γ (.case (.inl a) l r) (l.subst (Tm.singleSubst a)) D
  | right {Γ : VCtx τ} {a l r : Tm Φ} {A B D : τ}
      (ha : Tm.BranchValue Γ a B)
      (hl : Tm.HasType (A :: Γ) l D) (hr : Tm.HasType (B :: Γ) r D) :
      OperandBeta Γ (.case (.inr a) l r) (r.subst (Tm.singleSubst a)) D

/-- Expose beta at an instruction's exact input type. The unary site includes
ordinary returned calls. The case site keeps both typed reply continuations. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | letCall {Γ : VCtx τ} {L : LCtx τ} {a b : Tm Φ} {k : Region Φ} (p : Φ)
      (h : OperandBeta Γ a b (instrSrc p)) (hk : ValueBranches (instrTrg p :: Γ) k L) :
      Step Γ (.let₁ (.op p a) k) (.let₁ (.op p b) k) L
  | caseCall {Γ : VCtx τ} {L : LCtx τ} {a b : Tm Φ} {l r : Region Φ} {A B : τ} (p : Φ)
      (h : OperandBeta Γ a b (instrSrc p)) (hout : instrTrg p = coprod A B)
      (hl : ValueBranches (A :: Γ) l L) (hr : ValueBranches (B :: Γ) r L) :
      Step Γ (.case (.op p a) l r) (.case (.op p b) l r) L

abbrev Eqv (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) :=
  Paper.Extension.Eqv Step Γ r s L

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorCaseOperands
