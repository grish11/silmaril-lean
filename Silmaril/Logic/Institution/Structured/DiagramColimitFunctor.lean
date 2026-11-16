module

public import Silmaril.Logic.Institution.Structured.DiagramColimits

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.CoDiagram
open CategoryTheory CategoryTheory.Limits
universe u w x
noncomputable section
variable {C : Type w} [Category.{x} C] [HasColimitsOfSize.{u,u} C]
variable {D E F : CoDiagram.{u,u} C}

/-- A diagram map induces a cocone in its target diagram's actual colimit. -/
def colimitMapCocone (f : D ⟶ E) : Cocone D.I where
  pt := colimit E.I
  ι := {
    app := fun node => f.ρ.app node ≫ colimit.ι E.I (f.Φ.obj node)
    naturality := by
      intro i j g
      simp only [Functor.const_obj_map]
      rw [← Category.assoc, f.ρ.naturality g, Category.assoc]
      simp only [Functor.comp_map, colimit.w]
      exact (Category.comp_id _).symm }

/-- Map colimits along a change of node category and a diagram transformation. -/
def colimitMap (f : D ⟶ E) : colimit D.I ⟶ colimit E.I :=
  colimit.desc D.I (colimitMapCocone f)

@[reassoc (attr := simp)]
theorem ι_colimitMap (f : D ⟶ E) (node : D.Sign) :
    colimit.ι D.I node ≫ colimitMap f = f.ρ.app node ≫ colimit.ι E.I (f.Φ.obj node) :=
  colimit.ι_desc _ _

theorem colimitMap_id (D : CoDiagram.{u,u} C) : colimitMap (𝟙 D) = 𝟙 _ := by
  apply colimit.hom_ext
  intro node
  simp only [ι_colimitMap, CoDiagram.id_app, Category.id_comp, Category.comp_id]
  rfl

theorem colimitMap_comp (f : D ⟶ E) (g : E ⟶ F) :
    colimitMap (f ≫ g) = colimitMap f ≫ colimitMap g := by
  apply colimit.hom_ext
  intro node
  simp only [ι_colimitMap, CoDiagram.comp_app, Category.assoc, ι_colimitMap_assoc]
  rfl

/-- The genuine colimit functor on varying-shape diagrams. -/
def colimitFunctor : CoDiagram.{u,u} C ⥤ C where
  obj D := colimit D.I
  map := colimitMap
  map_id := colimitMap_id
  map_comp := colimitMap_comp

end
end Silmaril.Logic.Institution.CoDiagram
