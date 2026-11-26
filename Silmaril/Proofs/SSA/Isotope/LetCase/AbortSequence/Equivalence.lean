module

public import Silmaril.SSA.Isotope.LetCase.AbortSequence.Defs

public section

namespace Silmaril.Isotope.LetCase.LocallyNameless

universe u v w r

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν] {Γ : Ctx ν τ}
  {ε : Type r} [HasEff Φ ε] {pe : ε}
  {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}

theorem abortEquiv_symm_proof (h : AbortEquiv pe Γ β a b A) : AbortEquiv pe Γ β b a A := by
  induction h with
  | equiv h => exact .equiv h.symm
  | primitive h ha hb =>
    cases h with
    | sequence h => exact .primitive (.unsequence h) hb ha
    | unsequence h => exact .primitive (.sequence h) hb ha
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1
  | op _ ih => exact .op ih
  | let₁ _ _ ih1 ih2 => exact .let₁ ih1 ih2
  | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  | let₂ _ _ ih1 ih2 => exact .let₂ ih1 ih2
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih1 ih2 ih3 => exact .case ih1 ih2 ih3
  | abort _ ih => exact .abort ih

theorem abortCongr_into_proof {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A}
    (h : AbortCongr Γ da db) : AbortEquiv pe Γ β a b A := by
  induction h with
  | refl d => exact .equiv (.refl d.toHasType)
  | symm _ ih => exact abortEquiv_symm_proof ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sequence d =>
    exact .primitive (.sequence d.toHasType) (.abort d.toHasType) (.let₁ d.toHasType (.abort .bv))
  | op _ ih => exact .op ih
  | let₁ _ _ ih1 ih2 => exact .let₁ ih1 ih2
  | let₂ _ _ ih1 ih2 => exact .let₂ ih1 ih2
  | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih1 ih2 ih3 => exact .case ih1 ih2 ih3
  | abort _ ih => exact .abort ih

end Silmaril.Isotope.LetCase.LocallyNameless
