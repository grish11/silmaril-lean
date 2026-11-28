module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Reduction
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Validity is preserved by precomposition with a guarded region -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithAdministrativeReturns.WithGuardedTablePacking
open Semantics.Categorical
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false

/-- Two regions that are valid in every supported model stay valid after
a guarded region is run before them. -/
theorem Valid.seq {X Y Z : τ} {g r s : Region Φ} (hg : ValueBranches [X] g [Y])
    (hr : ValueBranches [Y] r [Z]) (hs : ValueBranches [Y] s [Z]) (v : Valid hr.hasType hs.hasType) :
    Valid (seqValueBranches hg hr).hasType (seqValueBranches hg hs).hasType :=
  fun J _ _ M _ _ shared => by
    have comp : ∀ (k : Region Φ) (hk : ValueBranches [Y] k [Z]),
        denoteSingletonRegion J M (seqValueBranches hg hk).hasType =
          denoteSingletonRegion J M hg.hasType ≫ denoteSingletonRegion J M hk.hasType := fun k hk => by
      rw [← Paper.TypeCategory.denoteArrow_ofRegion J M shared (seqValueBranches hg hk),
        ← Paper.TypeCategory.denoteArrow_ofRegion J M shared hg,
        ← Paper.TypeCategory.denoteArrow_ofRegion J M shared hk,
        ← Paper.TypeCategory.ofRegion_comp hg hk (seqValueBranches hg hk)]
      exact (Paper.TypeCategory.denoteFunctor (Φ := Φ) J M shared).map_comp _ _
    have inner : denoteSingletonRegion J M hr.hasType = denoteSingletonRegion J M hs.hasType := by
      unfold denoteSingletonRegion
      rw [v J M shared]
    have outer := (comp r hr).trans
      ((congrArg (denoteSingletonRegion J M hg.hasType ≫ ·) inner).trans (comp s hs).symm)
    unfold denoteSingletonRegion at outer
    have sec : J.map (singletonLabelPayload M Z) ≫ J.map (labelInject M 0 (L := [Z]) (A := Z) rfl) = 𝟙 _ := by
      rw [← J.map_comp, SingletonDispatcher.payload_labelInject, J.map_id]
    have left := (cancel_epi (J.map (λ_ (M.obj X)).inv)).1 outer
    have right := congrArg (· ≫ J.map (labelInject M 0 (L := [Z]) (A := Z) rfl)) left
    simpa only [Category.assoc, sec, Category.comp_id] using right

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
