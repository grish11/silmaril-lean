module

public import Silmaril.SSA.Isotope.Institution.Relational.Inclusions.Defs

public section

namespace Silmaril.Isotope.Institution.Relational

open Semantics

universe u v w q

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ] {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}
variable {D : τ → Type v} [ProductModel D] [UnitModel D] [CoproductModel D]

theorem seqCase_denoteRelation_proof (M : RelationModel D Φ)
    {t : Silmaril.Isotope.LetSeq.LocallyNameless.Tm ν Φ n}
    (d : Silmaril.Isotope.LetSeq.LocallyNameless.Derivation Φ Γ β t A) :
    ∀ (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (b : D A),
      (Morphism.SeqCase.derivation d).denoteRelation D M γ ρ b ↔
        d.denoteRelation D M γ ρ b := by
  induction d with
  | fv | bv | unit => intros; rfl
  | op _ ih =>
      intro γ ρ b
      exact exists_congr fun a => and_congr (ih γ ρ a) Iff.rfl
  | let₁ _ _ iha ihb =>
      intro γ ρ b
      exact exists_congr fun a => and_congr (iha γ ρ a) (ihb γ (ρ.snoc a) b)
  | pair _ _ iha ihb =>
      intro γ ρ p
      exact exists_congr fun a => and_congr (iha γ ρ a)
        (exists_congr fun b => and_congr (ihb γ ρ b) Iff.rfl)
  | let₂ _ _ iha ihb =>
      intro γ ρ b
      exact exists_congr fun ab =>
        let p := ProductModel.productEquiv (D := D) _ _ ab
        and_congr (iha γ ρ ab) (ihb γ ((ρ.snoc p.1).snoc p.2) b)

theorem caseIter_denoteRelation_proof (M : RelationModel D Φ)
    {t : Silmaril.Isotope.LetCase.LocallyNameless.Tm ν Φ n}
    (d : Silmaril.Isotope.LetCase.LocallyNameless.Derivation Φ Γ β t A) :
    ∀ (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (b : D A),
      (Morphism.CaseIter.derivation d).denoteRelation D M γ ρ b ↔
        d.denoteRelation D M γ ρ b := by
  induction d with
  | fv | bv | unit | abort => intros; rfl
  | op _ ih | inl _ ih | inr _ ih =>
      intro γ ρ b
      exact exists_congr fun a => and_congr (ih γ ρ a) Iff.rfl
  | let₁ _ _ iha ihb =>
      intro γ ρ b
      exact exists_congr fun a => and_congr (iha γ ρ a) (ihb γ (ρ.snoc a) b)
  | pair _ _ iha ihb =>
      intro γ ρ p
      exact exists_congr fun a => and_congr (iha γ ρ a)
        (exists_congr fun b => and_congr (ihb γ ρ b) Iff.rfl)
  | let₂ _ _ iha ihb =>
      intro γ ρ b
      exact exists_congr fun ab =>
        let p := ProductModel.productEquiv (D := D) _ _ ab
        and_congr (iha γ ρ ab) (ihb γ ((ρ.snoc p.1).snoc p.2) b)
  | case _ _ _ ihe ihl ihr =>
      intro γ ρ b
      refine exists_congr fun e => and_congr (ihe γ ρ e) ?_
      cases CoproductModel.coprodEquiv (D := D) _ _ e with
      | inl a => exact ihl γ (ρ.snoc a) b
      | inr a => exact ihr γ (ρ.snoc a) b

end Silmaril.Isotope.Institution.Relational
