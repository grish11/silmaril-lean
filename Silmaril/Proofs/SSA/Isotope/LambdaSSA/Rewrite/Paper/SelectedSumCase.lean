module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Selected.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

/-! # Structural denotation of selected sum cases -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCase

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_pre_map pair_maps_eq_map_lift)
open CartesianMonoidalCategory (lift)
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
    Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
  {X A : τ} {L : LCtx τ}

set_option backward.isDefEq.respectTransparency false in
omit [FreydCategory.CentralUnit J] in
theorem applyPacked_denotes {p : Region Φ} {hp : HasType [product X A] p L}
    {g : J.obj (M.obj (product X A)) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hp (J.map (λ_ (M.obj (product X A))).hom ≫ g))
    (unpacked : HasType [A, X] (Paper.PackedBody.applyPacked p) L) :
    RegionDenotes J M unpacked
      (J.map ((λ_ (M.obj X)).hom ▷ M.obj A) ≫ J.map (M.productIso X A).inv ≫ g) := by
  let σ : Nat → Tm Φ := Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.var ∘ (Nat.succ ∘ Nat.succ))
  let k := ((λ_ (M.obj X)).hom ▷ M.obj A) ≫ (M.productIso X A).inv
  have hPair : lift (lookup M 1 (rfl : At [A, X] 1 X)) (lookup M 0 (rfl : At [A, X] 0 A)) =
      ((λ_ (M.obj X)).hom ▷ M.obj A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [lookup, ctxObj, CartesianMonoidalCategory.leftUnitor_hom]
  have dv : Denotes J M (.pair (.var (i := 1) rfl) (.var (i := 0) rfl) :
      Tm.HasType [A, X] (σ 0) (product X A)) (J.map k) := by
    simpa only [pair_maps_eq_map_lift, ← J.map_comp, hPair, k] using
      Denotes.pair (Denotes.var (J := J) (M := M) (Φ := Φ) (rfl : At [A, X] 1 X))
        (Denotes.var (rfl : At [A, X] 0 A))
  obtain ⟨_, body⟩ := d.substSingleton J M σ dv
  simpa only [Paper.PackedBody.applyPacked, k, Category.assoc, ← J.map_comp_assoc,
    Iso.inv_hom_id, Category.comp_id, ← J.map_comp] using body

include shared in
set_option backward.isDefEq.respectTransparency false in
theorem arm_denotes (arm : CaseArm Φ X A L) :
    RegionDenotes J M arm.elaborate.property.hasType
      (J.map ((λ_ (M.obj X)).hom ▷ M.obj A) ≫ arm.targetArrow J M) := by
  have body := applyPacked_denotes J M (arm.body.targetDenotes J M shared)
    (Paper.PackedBody.applyPacked_typed arm.body.elaborate.property).hasType
  have renamed := body.renameLabels J M arm.exitRen
  simpa only [CaseArm.elaborate, CaseArm.targetArrow, Category.assoc,
    ← J.map_comp, labelInject_labelMap] using renamed

include shared in
set_option backward.isDefEq.respectTransparency false in
theorem case_denotes (p : SumCase Φ X L) :
    RegionDenotes J M p.elaborate.property.hasType (J.map (λ_ (M.obj X)).hom ≫ p.targetArrow J M) := by
  have dn := RegionDenotes.case (p.discriminator.targetDenotes J M)
    (arm_denotes J M shared p.onLeft) (arm_denotes J M shared p.onRight)
  simpa only [SumCase.elaborate, SumCase.targetArrow, Category.assoc, case_pre_map] using dn

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCase
