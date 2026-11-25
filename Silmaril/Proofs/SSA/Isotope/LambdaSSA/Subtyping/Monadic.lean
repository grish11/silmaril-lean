module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Monadic.Defs

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [InstructionModel Φ τ ε m]

omit [LawfulMonad m] in
theorem denote_spec_proof {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) :
    Denotes ε h (denote (ε := ε) (m := m) h) := by
  induction h with
  | var h => exact .var h
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | unit => exact .unit
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | sub _ d ih => exact .sub ih d

variable [Iterate m] [LawfulElgotMonad m]

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem regionDenotes_exists_proof {Γ : VCtx τ} {region : LambdaSSA.Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) :
    ∃ f, RegionDenotes (m := m) ε h f := by
  induction h with
  | br h ha => exact ⟨_, .br (h := h) (denote_spec_proof (ε := ε) ha)⟩
  | case he hl hr ihl ihr =>
      rcases ihl with ⟨fl, dl⟩
      rcases ihr with ⟨fr, dr⟩
      exact ⟨_, .case (denote_spec_proof (ε := ε) he) dl dr⟩
  | let₁ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₁ (denote_spec_proof (ε := ε) ha) db⟩
  | let₂ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₂ (denote_spec_proof (ε := ε) ha) db⟩
  | @cfg _ _ _ n _ R he hb ihe ihb =>
      cases n with
      | zero =>
          rcases ihe with ⟨fe, de⟩
          exact ⟨fe, .cfgZero he hb de⟩
      | succ n =>
          rcases ihe with ⟨fe, de⟩
          choose fb db using ihb
          rcases LambdaSSA.Semantics.Monadic.collectiveDenotes_exists_succ
            n _ R _ fb with ⟨fc, dc⟩
          exact ⟨_, .cfg he hb de db dc⟩

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic
