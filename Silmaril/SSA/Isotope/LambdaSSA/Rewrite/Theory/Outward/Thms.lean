module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.OutwardEffect

/-! # Effect-preserving outward CFG elimination and branch binding

The Freyd unit comparison is central when the value category shares the
computation category's tensor unit, as in Definition 5.3 of
*The Denotational Semantics of SSA* (arXiv:2411.09347v2).
-/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

/-- A CFG whose entry can reach only outward labels evaluates that entry,
even when it contains effectful operations or nested CFGs. -/
theorem denoteRegion_cfgOutward
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hr : Region.HasType Γ r L)
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (hs : Region.HasType Γ (.cfg (r.renameLabels (fun j => n + 1 + j)) (n + 1) blocks) L) :
    denoteRegion J M hs = denoteRegion J M hr := by
  obtain ⟨_, _, dr, ds⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgOutward_common J M hu R hr hb
  exact (RegionDenotes.eq_denote (h := hs) J M ds).symm.trans (RegionDenotes.eq_denote J M dr)

/-- Evaluating a typed branch argument in a let and then forwarding its
variable preserves the branch denotation, including the argument's effects. -/
theorem denoteRegion_branchBind
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ} {A : τ}
    (hℓ : At L ℓ A) (ha : Tm.HasType Γ a A) :
    denoteRegion J M (.br hℓ ha) =
      denoteRegion J M (.let₁ ha (.br hℓ (.var (i := 0) rfl))) := by
  obtain ⟨_, dr, ds⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.branchBind_common J M hu hℓ ha
  exact (RegionDenotes.eq_denote J M dr).symm.trans (RegionDenotes.eq_denote J M ds)

/-- A nonempty CFG that routes its entry to local blocks and whose blocks
only jump outward denotes one dispatch with the entry's context retained. -/
theorem denoteRegion_cfgLink
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hr : Region.HasType Γ r (List.ofFn R))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) L)
    (g : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ J.obj (labelObj M L))
    (hg : ∀ i, J.map (ctxObj M Γ ◁ finiteLabelInject M R i) ≫ g = denoteRegion J M (hb i))
    (hs : Region.HasType Γ
      (.cfg r (n + 1) (fun i => (blocks i).renameLabels (fun j => n + 1 + j))) L) :
    denoteRegion J M hs =
      Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend J (denoteRegion J M hr) ≫ J.map (ctxObj M Γ ◁ labelObjToFinite M R) ≫ g := by
  obtain ⟨_, d⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgLink_common J M hu R hr hb
    (denoteRegion_spec J M hr) (fun i => denoteRegion_spec J M (hb i)) g hg
  exact (RegionDenotes.eq_denote (h := hs) J M d).symm

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
