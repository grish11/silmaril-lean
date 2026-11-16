module

public import Silmaril.Logic.Institution.Structured.Theories.Models
public import Silmaril.Logic.Institution.Structured.DiagramColimitFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured
open CategoryTheory CategoryTheory.Limits Opposite Silmaril.Logic.Institution
universe u
noncomputable section
variable {Sign : Type u} [Category.{u} Sign]

/-- The node-theory model diagram appearing in Theorem 4.13. -/
def theoryModelDiagram (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I) :
    P.sig.Signᵒᵖ ⥤ Cat.{u,u} :=
  ((J I).obj P).I.op ⋙ SemanticModels.modelFunctor I.toRoomFunctor

/-- A compatible global model of the presentation satisfies all consequences
at every node, by the actual definition of node consequences. -/
theorem nodeModels_mem (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I)
    (node : P.sig.Sign) (M : SemanticModels.Models (institution I) P) :
    Theory.modelsProperty (nodeTheory I P node).axioms
      ((projection I P.sig node).toFunctor.obj M.obj) := by
  intro φ hφ
  exact hφ M.obj M.property

/-- Project a model of the structured theory to its local theory model.
The functor also projects model morphisms, rather than only objects. -/
def nodeModelProjection (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I)
    (node : P.sig.Sign) : SemanticModels.Models (institution I) P ⥤
      SemanticModels.Models I.toRoomFunctor (nodeTheory I P node) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (projection I P.sig node).toFunctor) (nodeModels_mem I P node)

/-- The projected local theory models agree along every diagram edge. -/
theorem nodeModelProjection_edge (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) {i j : P.sig.Sign} (f : i ⟶ j) :
    nodeModelProjection I P j ⋙
      SemanticModels.reduct I.toRoomFunctor (((J I).obj P).I.map f) =
      nodeModelProjection I P i := by
  exact (Theory.lift_ι_comp_eq_comp _ _ _ _ _ _
    (congrArg Cat.Hom.toFunctor (projection_edge I P.sig f).symm) _ _ _).symm

/-- The actual comparison cone from structured-theory models to the diagram
of node-theory model categories (the first limit in Theorem 4.13). -/
def theoryModelCone (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I) :
    Cone (theoryModelDiagram I P) where
  pt := Cat.of (SemanticModels.Models (institution I) P)
  π := {
    app := fun node => (nodeModelProjection I P node.unop).toCatHom
    naturality := by
      intro i j f
      change 𝟙 _ ≫ (nodeModelProjection I P j.unop).toCatHom =
        (nodeModelProjection I P i.unop ⋙
          SemanticModels.reduct I.toRoomFunctor (((J I).obj P).I.map f.unop)).toCatHom
      rw [Category.id_comp]
      exact congrArg Functor.toCatHom (nodeModelProjection_edge I P f.unop).symm }

/-- Forget the axiom-satisfaction witness at each local model category. -/
def theoryModelInclusion (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I) :
    theoryModelDiagram I P ⟶ modelDiagram I P.sig where
  app := fun _ => (ObjectProperty.ι _).toCatHom
  naturality := by
    intro i j f
    rfl

/-- Every cone of local theory models is also a cone of underlying signature models. -/
def underlyingTheoryModelCone (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) (s : Cone (theoryModelDiagram I P)) : Cone (modelDiagram I P.sig) :=
  (Cone.postcompose (theoryModelInclusion I P)).obj s

/-- Assemble an arbitrary cone's local models as a compatible global signature model. -/
def underlyingTheoryModelLift (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) (s : Cone (theoryModelDiagram I P)) : s.pt ⟶ Models I P.sig :=
  Cat.HasLimits.limitConeLift _ (underlyingTheoryModelCone I P s)

/-- The assembled global model has exactly the prescribed local signature models. -/
theorem underlyingTheoryModelLift_fac (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) (s : Cone (theoryModelDiagram I P)) (node : P.sig.Sign) :
    underlyingTheoryModelLift I P s ≫ projection I P.sig node =
      s.π.app (op node) ≫ (ObjectProperty.ι _).toCatHom :=
  (Cat.HasLimits.limitConeIsLimit (modelDiagram I P.sig)).fac
    (underlyingTheoryModelCone I P s) (op node)

/-- Assembled compatible models satisfy the original global axioms. -/
theorem underlyingTheoryModelLift_mem (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) (s : Cone (theoryModelDiagram I P)) (M : s.pt) :
    Theory.modelsProperty P.axioms ((underlyingTheoryModelLift I P s).toFunctor.obj M) := by
  intro φ hφ
  rcases φ with ⟨node, φ⟩
  have hmem : φ ∈ nodeConsequences I P node := (room I P.sig).subset_closure _ hφ
  have hsat := ((s.π.app (op node)).toFunctor.obj M).property φ hmem
  have he := congrArg (fun k => k.toFunctor.obj M) (underlyingTheoryModelLift_fac I P s node)
  change I.Sat (P.sig.I.obj node)
    ((underlyingTheoryModelLift I P s ≫ projection I P.sig node).toFunctor.obj M) φ
  rw [he]
  exact hsat

/-- Lift any cone of node-theory models into the original structured-theory
model category, including its compatible model morphisms. -/
def theoryModelLift (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) (s : Cone (theoryModelDiagram I P)) :
    s.pt ⟶ Cat.of (SemanticModels.Models (institution I) P) :=
  (ObjectProperty.lift _ (underlyingTheoryModelLift I P s).toFunctor
    (underlyingTheoryModelLift_mem I P s)).toCatHom

private theorem fullSubcategory_functor_ext {C D : Type u} [Category.{u} C] [Category.{u} D]
    (Q : ObjectProperty D) {F G : C ⥤ Q.FullSubcategory}
    (h : F ⋙ Q.ι = G ⋙ Q.ι) : F = G := by
  have hobj : ∀ X, F.obj X = G.obj X := fun X =>
    ObjectProperty.FullSubcategory.ext (congrArg (fun K => K.obj X) h)
  refine CategoryTheory.Functor.ext hobj ?_
  intro X Y f
  apply Q.ι.map_injective
  simpa only [Functor.comp_map, Functor.map_comp, eqToHom_map] using Functor.congr_hom h f

/-- The assembled theory-model functor recovers every prescribed local model
and every prescribed local model morphism. -/
theorem theoryModelLift_fac (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) (s : Cone (theoryModelDiagram I P)) (node : P.sig.Sign) :
    theoryModelLift I P s ≫ (nodeModelProjection I P node).toCatHom = s.π.app (op node) := by
  apply Cat.Hom.ext
  apply fullSubcategory_functor_ext (Theory.modelsProperty (nodeTheory I P node).axioms)
  exact congrArg Cat.Hom.toFunctor (underlyingTheoryModelLift_fac I P s node)

/-- Any functor recovering the given local theory models is the assembled one. -/
theorem theoryModelLift_unique (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) (s : Cone (theoryModelDiagram I P))
    (m : s.pt ⟶ Cat.of (SemanticModels.Models (institution I) P))
    (hm : ∀ node, m ≫ (nodeModelProjection I P node.unop).toCatHom = s.π.app node) :
    m = theoryModelLift I P s := by
  apply Cat.Hom.ext
  apply fullSubcategory_functor_ext (Theory.modelsProperty P.axioms)
  have hu : (m.toFunctor ⋙ ObjectProperty.ι _).toCatHom =
      underlyingTheoryModelLift I P s := by
    apply (Cat.HasLimits.limitConeIsLimit (modelDiagram I P.sig)).hom_ext
    intro node
    change (m.toFunctor ⋙ ObjectProperty.ι _).toCatHom ≫ projection I P.sig node.unop =
      underlyingTheoryModelLift I P s ≫ projection I P.sig node.unop
    rw [underlyingTheoryModelLift_fac]
    exact congrArg (fun k => k ≫ (ObjectProperty.ι _).toCatHom) (hm node)
  exact congrArg Cat.Hom.toFunctor hu

/-- Structured-theory models form the actual limit of the node-theory model
categories, including model morphisms (Theorem 4.13, first comparison). -/
def theoryModelConeIsLimit (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) : IsLimit (theoryModelCone I P) where
  lift := theoryModelLift I P
  fac := fun s node => theoryModelLift_fac I P s node.unop
  uniq := fun s m hm => theoryModelLift_unique I P s m hm

/-- The model cone of the actual colimit of node theories. -/
def colimitTheoryModelCone (I : ClassicInstitution.{u,u,u,u,u} Sign)
    [HasColimitsOfSize.{u,u} (Spec I.toRoomFunctor)] (P : StructuredTheory I) :
    Cone (theoryModelDiagram I P) :=
  (SemanticModels.modelFunctor I.toRoomFunctor).mapCone
    (colimit.cocone ((J I).obj P).I).op

/-- Original exactness makes the colimit theory's model cone limiting. -/
def colimitTheoryModelConeIsLimit (I : ClassicInstitution.{u,u,u,u,u} Sign)
    [HasColimitsOfSize.{u,u} (Spec I.toRoomFunctor)]
    (hExact : SemanticModels.Exact I.toRoomFunctor) (P : StructuredTheory I) :
    IsLimit (colimitTheoryModelCone I P) := by
  letI : PreservesColimitsOfSize.{u,u}
      (SemanticModels.institution I.toRoomFunctor ⋙ Room.modFunctor) := hExact
  have : PreservesLimitsOfSize.{u,u} (SemanticModels.modelFunctor I.toRoomFunctor) :=
    preservesLimitsOfSize_leftOp (SemanticModels.institution I.toRoomFunctor ⋙ Room.modFunctor)
  exact isLimitOfPreserves (SemanticModels.modelFunctor I.toRoomFunctor)
    (colimit.isColimit ((J I).obj P).I).op

/-- Structured-theory models are isomorphic, as categories, to models of the
actual node-theory colimit under original exactness and theory cocompleteness
(Theorem 4.13). Naturality is established separately. -/
def modelComparisonIso (I : ClassicInstitution.{u,u,u,u,u} Sign)
    [HasColimitsOfSize.{u,u} (Spec I.toRoomFunctor)]
    (hExact : SemanticModels.Exact I.toRoomFunctor) (P : StructuredTheory I) :
    Cat.of (SemanticModels.Models (institution I) P) ≅
      Cat.of (SemanticModels.Models I.toRoomFunctor (colimit ((J I).obj P).I)) :=
  (theoryModelConeIsLimit I P).conePointUniqueUpToIso
    (colimitTheoryModelConeIsLimit I hExact P)

/-- Local theory-model projections commute with reduct along a structured
semantic theory map. -/
theorem nodeModelProjection_map (I : ClassicInstitution.{u,u,u,u,u} Sign)
    {P Q : StructuredTheory I} (f : P ⟶ Q) (node : P.sig.Sign) :
    SemanticModels.reduct (institution I) f ⋙ nodeModelProjection I P node =
      nodeModelProjection I Q (f.sig.Φ.obj node) ⋙
        SemanticModels.reduct I.toRoomFunctor (((J I).map f).ρ.app node) := by
  apply fullSubcategory_functor_ext (Theory.modelsProperty (nodeTheory I P node).axioms)
  exact congrArg (fun k => ObjectProperty.ι (Theory.modelsProperty Q.axioms) ⋙ k.toFunctor)
    (reduct_projection I f.sig node)

/-- Assemble each structured presentation into its actual colimit theory. -/
def assembledTheoryFunctor (I : ClassicInstitution.{u,u,u,u,u} Sign)
    [HasColimitsOfSize.{u,u} (Spec I.toRoomFunctor)] :
    StructuredTheory I ⥤ Spec I.toRoomFunctor := J I ⋙ CoDiagram.colimitFunctor

/-- The inverse comparison projects to the reduct along the colimit injection. -/
theorem modelComparisonIso_inv_projection (I : ClassicInstitution.{u,u,u,u,u} Sign)
    [HasColimitsOfSize.{u,u} (Spec I.toRoomFunctor)]
    (hExact : SemanticModels.Exact I.toRoomFunctor) (P : StructuredTheory I)
    (node : P.sig.Sign) :
    (modelComparisonIso I hExact P).inv ≫ (nodeModelProjection I P node).toCatHom =
      (SemanticModels.reduct I.toRoomFunctor (colimit.ι ((J I).obj P).I node)).toCatHom :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (op node)

/-- The actual model-category comparison commutes with every structured
semantic theory map, including its change of node category. -/
theorem modelComparisonIso_inv_naturality (I : ClassicInstitution.{u,u,u,u,u} Sign)
    [HasColimitsOfSize.{u,u} (Spec I.toRoomFunctor)]
    (hExact : SemanticModels.Exact I.toRoomFunctor) {P Q : StructuredTheory I} (f : P ⟶ Q) :
    (SemanticModels.reduct I.toRoomFunctor ((assembledTheoryFunctor I).map f)).toCatHom ≫
        (modelComparisonIso I hExact P).inv =
      (modelComparisonIso I hExact Q).inv ≫ (SemanticModels.reduct (institution I) f).toCatHom := by
  apply (theoryModelConeIsLimit I P).hom_ext
  intro node
  change _ ≫ (nodeModelProjection I P node.unop).toCatHom =
    _ ≫ (nodeModelProjection I P node.unop).toCatHom
  rw [Category.assoc, modelComparisonIso_inv_projection, Category.assoc]
  change _ = (modelComparisonIso I hExact Q).inv ≫
    (SemanticModels.reduct (institution I) f ⋙ nodeModelProjection I P node.unop).toCatHom
  rw [nodeModelProjection_map]
  change _ = (modelComparisonIso I hExact Q).inv ≫
    (nodeModelProjection I Q (f.sig.Φ.obj node.unop)).toCatHom ≫
      (SemanticModels.reduct I.toRoomFunctor (((J I).map f).ρ.app node.unop)).toCatHom
  rw [← Category.assoc, modelComparisonIso_inv_projection]
  change (SemanticModels.reduct I.toRoomFunctor ((assembledTheoryFunctor I).map f) ⋙
      SemanticModels.reduct I.toRoomFunctor (colimit.ι ((J I).obj P).I node.unop)).toCatHom =
    (SemanticModels.reduct I.toRoomFunctor (colimit.ι ((J I).obj Q).I (f.sig.Φ.obj node.unop)) ⋙
      SemanticModels.reduct I.toRoomFunctor (((J I).map f).ρ.app node.unop)).toCatHom
  rw [← SemanticModels.reduct_comp, ← SemanticModels.reduct_comp]
  exact congrArg (fun k => (SemanticModels.reduct I.toRoomFunctor k).toCatHom)
    (CoDiagram.ι_colimitMap ((J I).map f) node.unop)

end
end Silmaril.Logic.Institution.Structured
