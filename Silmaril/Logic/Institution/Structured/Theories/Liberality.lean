module

public import Silmaril.Logic.Institution.Structured.Theories.ModelComparison
public import Mathlib.CategoryTheory.Adjunction.Basic

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution
universe u
noncomputable section
variable {Sign : Type u} [Category.{u} Sign]

/-- Every structured-theory reduct is conjugate to the actual colimit-theory
reduct by the proved model-category comparison isomorphisms. -/
theorem structured_reduct_conjugate (I : ClassicInstitution.{u,u,u,u,u} Sign)
    [HasColimitsOfSize.{u,u} (Spec I.toRoomFunctor)]
    (hExact : SemanticModels.Exact I.toRoomFunctor) {P Q : StructuredTheory I} (f : P ⟶ Q) :
    SemanticModels.reduct (institution I) f =
      (modelComparisonIso I hExact Q).hom.toFunctor ⋙
        SemanticModels.reduct I.toRoomFunctor ((assembledTheoryFunctor I).map f) ⋙
          (modelComparisonIso I hExact P).inv.toFunctor := by
  have h : (SemanticModels.reduct (institution I) f).toCatHom =
      (modelComparisonIso I hExact Q).hom ≫
        (SemanticModels.reduct I.toRoomFunctor ((assembledTheoryFunctor I).map f)).toCatHom ≫
          (modelComparisonIso I hExact P).inv := by
    rw [modelComparisonIso_inv_naturality, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact congrArg Cat.Hom.toFunctor h

/-- Original liberality and exactness, together with original theory
cocompleteness, imply structured liberality (Durán–Meseguer 1999, Theorem 4.13).
The adjoints are transported through actual natural comparison isomorphisms. -/
theorem structured_liberal (I : ClassicInstitution.{u,u,u,u,u} Sign)
    [HasColimitsOfSize.{u,u} (Spec I.toRoomFunctor)]
    (hLiberal : SemanticModels.Liberal I.toRoomFunctor)
    (hExact : SemanticModels.Exact I.toRoomFunctor) :
    SemanticModels.Liberal (institution I) := by
  intro P Q f
  have : ((modelComparisonIso I hExact Q).hom.toFunctor).IsRightAdjoint :=
    (Cat.equivOfIso (modelComparisonIso I hExact Q)).symm.toAdjunction.isRightAdjoint
  have : ((modelComparisonIso I hExact P).inv.toFunctor).IsRightAdjoint :=
    (Cat.equivOfIso (modelComparisonIso I hExact P)).toAdjunction.isRightAdjoint
  have : (SemanticModels.reduct I.toRoomFunctor ((assembledTheoryFunctor I).map f)).IsRightAdjoint :=
    hLiberal ((assembledTheoryFunctor I).map f)
  rw [structured_reduct_conjugate I hExact f]
  infer_instance

end
end Silmaril.Logic.Institution.Structured
