module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.BranchNormalization

/-! # Typed, effect-preserving normalization of every branch argument -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Region

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits

/-- Substitution after normalizing a branch binds the original argument once
and evaluates the continuation beneath that binder. -/
theorem lsubst_bindBranchArguments_br {Φ : Type u₄} (ℓ : Nat) (a : Tm Φ)
    (σ : Nat → Region Φ) :
    (Region.br ℓ a).bindBranchArguments.lsubst σ = .let₁ a (σ ℓ) := by
  change Region.let₁ a (compLSubst labelId σ ℓ) = _
  rw [compLSubst_id_left]

variable {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]

/-- Branch normalization retains the exact input and exit interface and
makes each branch argument a constructor value. -/
theorem HasType.bindBranchArguments {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : HasType Γ r L) : ValueBranches Γ r.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.bindBranchArguments_valueBranches hr

/-- After binding branch arguments, native label substitution respects
equivalence between arbitrary continuation bodies at every typed entry. -/
theorem HasType.bindBranchArguments_lsubst_equivalent {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : HasType Γ r L) {σ σ' : Nat → Region Φ} (h : LSubst.Equivalent Γ L K σ σ') :
    RewriteEquiv Γ (r.bindBranchArguments.lsubst σ) (r.bindBranchArguments.lsubst σ') K :=
  hr.bindBranchArguments.lsubst_equivalent h

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- Binding each branch argument before jumping retains its denotation, also
under nested CFGs and for effectful computations. -/
theorem denoteRegion_bindBranchArguments
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : HasType Γ r L) :
    denoteRegion J M hr = denoteRegion J M hr.bindBranchArguments.hasType := by
  obtain ⟨_, _, dr, ds⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.bindBranchArguments_common J M hu hr
  exact (RegionDenotes.eq_denote J M dr).symm.trans (RegionDenotes.eq_denote J M ds)

end Silmaril.Isotope.LambdaSSA.Region
