module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Defs

/-! # Structural proofs for the abort-sequencing extension -/

public section

namespace Silmaril.Isotope.LetIter.LocallyNameless.AbortEquiv

universe u v w r

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν] {ε : Type r} [HasEff Φ ε]
  {pe : ε} {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}

theorem symm_proof (h : AbortEquiv pe Γ β a b A) : AbortEquiv pe Γ β b a A := by
  induction h with
  | equiv h => exact .equiv h.symm
  | primitive law ha hb =>
    cases law with
    | sequence hs => exact .primitive (.unsequence hs) hb ha
    | unsequence hs => exact .primitive (.sequence hs) hb ha
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁
  | op _ ih => exact .op ih
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .abort ih
  | iter _ _ ih₁ ih₂ => exact .iter ih₁ ih₂

end Silmaril.Isotope.LetIter.LocallyNameless.AbortEquiv
