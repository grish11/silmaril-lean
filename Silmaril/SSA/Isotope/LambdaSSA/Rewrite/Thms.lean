module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Typing
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Soundness

/-! # Categorical soundness of typed CFG entry rewrites

Formation and soundness use the exact λSSA types and the existing structural
denotation into a coproduct of all exit argument types. Local entry unfolding
uses the Elgot fixpoint law. Coherence of the region denotation graph lets
the soundness theorem compare the chosen arrows of both endpoints.
-/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

section Formation

variable {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]

theorem Tm.BranchValue.hasType {Γ : VCtx τ} {a : Tm Φ} {A : τ}
    (h : Tm.BranchValue Γ a A) : Tm.HasType Γ a A :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.branchValue_hasType h

theorem Region.CfgEquiv.typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.CfgEquiv Γ r s L) : Region.HasType Γ r L ∧ Region.HasType Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgEquiv_typed h

end Formation

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Values

variable (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- A constructor branch value has a denotation in the image of the value functor. -/
theorem Tm.BranchValue.denotes_map {Γ : VCtx τ} {a : Tm Φ} {A : τ}
    (h : Tm.BranchValue Γ a A) :
    ∃ p : ctxObj M Γ ⟶ M.obj A, Denotes J M h.hasType (J.map p) := by
  obtain ⟨_, p, hp⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.branchValue_denotes J M h
  exact ⟨p, hp⟩

end Values

section Region

variable [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- An outward entry branch can leave its CFG directly with the same arrow. -/
theorem cfgBrExit_common {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ}
    {A : τ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hℓ : At L ℓ A) (ha : Tm.BranchValue Γ a A)
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ (hs : Region.HasType Γ (.cfg (.br (n + 1 + ℓ) a) (n + 1) blocks) L)
      (ht : Region.HasType Γ (.br ℓ a) L), ∃ f, RegionDenotes J M hs f ∧ RegionDenotes J M ht f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgBrExit_common J M R hℓ ha hb

/-- Binding a local branch argument directly into its block yields the same CFG arrow. -/
theorem cfgBrLocal_common {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ}
    {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (i : Fin (n + 1)) (ha : Tm.BranchValue Γ a (R i))
    (hb : ∀ j, Region.HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    ∃ (hs : Region.HasType Γ (.cfg (.br i a) (n + 1) blocks) L)
      (ht : Region.HasType Γ (.cfg (.let₁ a (blocks i)) (n + 1) blocks) L),
      ∃ f, RegionDenotes J M hs f ∧ RegionDenotes J M ht f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgBrLocal_common J M R i ha hb

/-- Equivalent regions in the CFG entry theory have equal chosen categorical denotations. -/
theorem Region.CfgEquiv.sound [RegionTypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Region.CfgEquiv Γ r s L)
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  obtain ⟨_, _, _, dr, ds⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgEquiv_common J M h
  exact (RegionDenotes.eq_denote (h := hr) J M dr).symm.trans
    (RegionDenotes.eq_denote (h := hs) J M ds)

end Region

end Silmaril.Isotope.LambdaSSA
