module

public import Silmaril.SSA.Isotope.LetCase.AbortSequence.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.AbortSequence.Equivalence

/-! # Empty sequencing and its LetIter inclusion -/

public section

namespace Silmaril.Isotope.LetCase.LocallyNameless

universe u v w r

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν] {Γ : Ctx ν τ}
  {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}

theorem AbortSequence.toLetIter (h : AbortSequence Γ β a b A) :
    LetIter.LocallyNameless.AbortSequence Γ β (Morphism.CaseIter.embed a)
      (Morphism.CaseIter.embed b) A := by
  cases h with
  | sequence h => exact .sequence (Morphism.CaseIter.embed_hasType h)
  | unsequence h => exact .unsequence (Morphism.CaseIter.embed_hasType h)

variable {ε : Type r} [HasEff Φ ε] {pe : ε}

theorem AbortEquiv.sequence (ha : HasType Φ Γ β a Silmaril.empty) :
    AbortEquiv pe Γ β (.abort a) (.let₁ a (.abort (.bv 0))) A :=
  .primitive (.sequence ha) (.abort ha) (.let₁ ha (.abort .bv))

theorem AbortEquiv.symm (h : AbortEquiv pe Γ β a b A) : AbortEquiv pe Γ β b a A :=
  abortEquiv_symm_proof h

/-- The inclusion carries the opt-in rules to their matching orientations. -/
theorem AbortEquiv.toLetIter (h : AbortEquiv pe Γ β a b A) :
    LetIter.LocallyNameless.AbortEquiv pe Γ β (Morphism.CaseIter.embed a)
      (Morphism.CaseIter.embed b) A :=
  Morphism.CaseIter.embed_refinement (fun h => h.toLetIter) h

theorem AbortCongr.toAbortEquiv {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A}
    (h : AbortCongr Γ da db) : AbortEquiv pe Γ β a b A :=
  abortCongr_into_proof h

end Silmaril.Isotope.LetCase.LocallyNameless
