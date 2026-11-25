module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Closure
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ClosureValues
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ClosureGenerators

/-! # Congruence under arbitrary typed continuation substitution -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem SubstitutionEquiv.typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) : HasType Γ r L ∧ HasType Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.substitutionEquiv_typed h

/-- Apply any exactly typed family of continuation bodies to both sides of
an equation. The continuations may themselves contain nested CFGs. -/
theorem SubstitutionEquiv.lsubst {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    SubstitutionEquiv Γ (r.lsubst σ) (s.lsubst σ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.substitutionEquiv_lsubst h hσ

/-- Apply simultaneous value substitution with constructor-valued images. -/
theorem SubstitutionEquiv.substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    SubstitutionEquiv Δ (r.substVars σ) (s.substVars σ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.substitutionEquiv_substVars h hσ

/-- Substitute equivalent continuations at constructor-valued branch arguments. -/
theorem ValueBranches.lsubst_substitutionEquiv {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ υ : Nat → Region Φ}
    (h : ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ ℓ) (υ ℓ) K) :
    SubstitutionEquiv Γ (r.lsubst σ) (r.lsubst υ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.lsubst_substitutionEquiv hr h

/-- Change both the entry and its continuation family. The initial entry
has value branches, so replacing the continuation argument is effect-safe. -/
theorem SubstitutionEquiv.lsubst_congr {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (h : SubstitutionEquiv Γ r s L) {σ υ : Nat → Region Φ}
    (hσ : ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ ℓ) (υ ℓ) K) :
    SubstitutionEquiv Γ (r.lsubst σ) (s.lsubst υ) K :=
  (hr.lsubst_substitutionEquiv hσ).trans (h.lsubst (fun _ _ hi => (hσ hi).typed.2))

/-- Native continuation composition is congruent in both families when
the first source family supplies constructor-valued branch arguments. -/
theorem LSubst.comp_substitutionEquiv {Γ : VCtx τ} {L K P : LCtx τ}
    {σ σ' υ υ' : Nat → Region Φ}
    (hσ : ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ ℓ) (σ' ℓ) K)
    (hυ : ∀ ⦃ℓ A⦄, At K ℓ A → SubstitutionEquiv (A :: Γ) (υ ℓ) (υ' ℓ) P)
    (hvalues : ∀ ⦃ℓ A⦄, At L ℓ A → ValueBranches (A :: Γ) (σ ℓ) K) :
    ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (compLSubst σ υ ℓ) (compLSubst σ' υ' ℓ) P :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.compLSubst_substitutionEquiv hσ hυ hvalues

/-- Pure let β for an arbitrary typed body is the substitution instance
of pure let β for an immediate branch to the bound variable. -/
theorem RewriteEquiv.letValue_instance {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {a : Tm Φ} {A : τ}
    (ha : Tm.BranchValue Γ a A) (hr : HasType (A :: Γ) r L) :
    ∃ (x y : Region Φ) (σ : Nat → Region Φ),
      RewriteEquiv Γ x y [A] ∧ LSubst.HasType Γ [A] L σ ∧
      x.lsubst σ = .let₁ a r ∧ y.lsubst σ = r.substVars (Tm.singleSubst a) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.letValue_instance ha hr

/-- An outward-only CFG is a substitution instance of the outward-entry
branch rule. The substituted continuation ignores its dummy unit argument. -/
theorem RewriteEquiv.cfgOutward_instance {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {blocks : Fin (n + 1) → Region Φ} (R : Fin (n + 1) → τ) (hr : HasType Γ r L)
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ (x y : Region Φ) (σ : Nat → Region Φ),
      RewriteEquiv Γ x y (Silmaril.unit :: L) ∧ LSubst.HasType Γ (Silmaril.unit :: L) L σ ∧
      x.lsubst σ = .cfg (r.renameLabels (fun j => n + 1 + j)) (n + 1) blocks ∧ y.lsubst σ = r :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgOutward_instance R hr hb

end Silmaril.Isotope.LambdaSSA.Region
