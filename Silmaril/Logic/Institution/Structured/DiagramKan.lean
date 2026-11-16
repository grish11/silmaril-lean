module

public import Silmaril.Logic.Institution.Pi.Defs
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.CoDiagram
open CategoryTheory
universe u w x
noncomputable section
variable {C : Type w} [Category.{x} C]
variable (D : CoDiagram.{u,u} C) {B : Type u} [Category.{u} B] (F : D.Sign ⥤ B)
variable [Functor.HasLeftKanExtension F D.I]

/-- Move a diagram onto a new shape by actual left Kan extension. This is the
shape-change operation used in Durán–Meseguer, Lemma 3.4. -/
def lanDiagram : CoDiagram.{u,u} C :=
  ⟨B, F.leftKanExtension D.I⟩

/-- The canonical diagram map into its left Kan extension. -/
def lanInclusion : D ⟶ lanDiagram D F where
  Φ := F
  ρ := F.leftKanExtensionUnit D.I

/-- Factor a diagram transformation through the Kan extension, keeping the
chosen outgoing shape functor as explicit data. -/
def lanDesc {E : CoDiagram.{u,u} C} (G : B ⥤ E.Sign)
    (α : D.I ⟶ F ⋙ (G ⋙ E.I)) : lanDiagram D F ⟶ E where
  Φ := G
  ρ := Functor.descOfIsLeftKanExtension _ (F.leftKanExtensionUnit D.I) _ α

/-- The universal factorization on each node; this is the diagram-map form of
left Kan extension, with its shape functors retained. -/
theorem lanDesc_fac {E : CoDiagram.{u,u} C} (G : B ⥤ E.Sign)
    (α : D.I ⟶ F ⋙ (G ⋙ E.I)) :
    F.leftKanExtensionUnit D.I ≫ Functor.whiskerLeft F (lanDesc D F G α).ρ = α := by
  exact Functor.descOfIsLeftKanExtension_fac _ (F.leftKanExtensionUnit D.I) _ α

/-- Uniqueness of the value transformation for a fixed outgoing shape functor. -/
theorem lanDesc_unique {E : CoDiagram.{u,u} C} (G : B ⥤ E.Sign)
    (α : D.I ⟶ F ⋙ (G ⋙ E.I))
    (β : (F.leftKanExtension D.I) ⟶ G ⋙ E.I)
    (h : F.leftKanExtensionUnit D.I ≫ Functor.whiskerLeft F β = α) :
    β = (lanDesc D F G α).ρ := by
  exact Functor.hom_ext_of_isLeftKanExtension _ (F.leftKanExtensionUnit D.I) _ _
    (h.trans (lanDesc_fac D F G α).symm)


/-- The factorization is an equality of actual diagram maps, including the
associator that identifies their composite shape functors. -/
theorem lanInclusion_desc {E : CoDiagram.{u,u} C} (G : B ⥤ E.Sign)
    (α : D.I ⟶ F ⋙ (G ⋙ E.I)) :
    lanInclusion D F ≫ lanDesc D F G α =
      (⟨F ⋙ G, α ≫ (Functor.associator F G E.I).inv⟩ : Diagram.CoHom D E) := by
  apply Diagram.CoHom.ext
    (f := lanInclusion D F ≫ lanDesc D F G α)
    (g := ⟨F ⋙ G, α ≫ (Functor.associator F G E.I).inv⟩) rfl
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext node
  simp [CoDiagram.comp_app, lanInclusion, lanDesc]

end

/-- Cocompleteness supplies the left Kan extensions used to change small
shapes; no extension-existence assumption is needed in this case. -/
theorem hasLeftKanExtension_of_cocomplete
    {C : Type w} [Category.{x} C] [CategoryTheory.Limits.HasColimitsOfSize.{u,u} C]
    (D : CoDiagram.{u,u} C) {B : Type u} [Category.{u} B] (F : D.Sign ⥤ B) :
    Functor.HasLeftKanExtension F D.I := by
  infer_instance

end Silmaril.Logic.Institution.CoDiagram
