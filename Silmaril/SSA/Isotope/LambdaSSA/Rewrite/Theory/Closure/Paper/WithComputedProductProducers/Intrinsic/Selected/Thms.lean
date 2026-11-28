module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Selected.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedProductDenotation

/-! # Structural witnesses for the selected elaboration -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] {X D : τ}

omit [FreydCategory.CentralUnit J] in
theorem orderedPair_eq_pair {A B : τ} (f : J.obj (M.obj X) ⟶ J.obj (M.obj A))
    (g : J.obj (M.obj X) ⟶ J.obj (M.obj B)) :
    orderedPair J M f g =
      Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair J f g ≫ J.map (M.productIso A B).inv :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedProductDenotation.orderedPair_eq_pair J M f g

/-- The expression graph contains the selected interpretation, at the exact
typing and with the empty input prefix accounted for. -/
theorem Term.targetDenotes (t : Term Φ X D) :
    Denotes J M t.elaborate.property (J.map (λ_ (M.obj X)).hom ≫ t.targetArrow J M) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedProductDenotation.term_selected J M t

variable (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
  Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)

include shared in
/-- The region graph contains the target generator fold at the actual
elaborated singleton region. The proof transports selected graph witnesses
through lowering and value substitution. -/
theorem Program.targetDenotes (p : Program Φ X D) :
    RegionDenotes J M p.elaborate.property.hasType
      (J.map (λ_ (M.obj X)).hom ≫ p.targetArrow J M ≫ J.map (labelInject M 0 (L := [D]) rfl)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedProductDenotation.program_selected J M shared p

include shared in
/-- A structurally certified region arrow selected by the intrinsic annotation. -/
@[expose] noncomputable def Program.selectedEvaluation (p : Program Φ X D) :
    {g : J.obj (ctxObj M [X]) ⟶ J.obj (labelObj M [D]) // RegionDenotes J M p.elaborate.property.hasType g} :=
  ⟨_, p.targetDenotes J M shared⟩

/-- Removing the empty input prefix and the singleton exit wrapper gives
the explicit generator interpretation in the target. -/
theorem Program.selectedEvaluation_eq_target (p : Program Φ X D) :
    J.map (λ_ (M.obj X)).inv ≫ (p.selectedEvaluation J M shared).val ≫ J.map (singletonLabelPayload M D) =
      p.targetArrow J M := by
  dsimp only [Program.selectedEvaluation]
  simp only [ctxObj, Category.assoc, ← J.map_comp_assoc, Iso.inv_hom_id,
    J.map_id, Category.id_comp, ← J.map_comp,
    Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher.labelInject_payload,
    Category.comp_id]

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic
