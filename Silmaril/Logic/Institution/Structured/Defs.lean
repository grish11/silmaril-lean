module

public import Silmaril.Logic.Institution.Pi.Defs
public import Mathlib.CategoryTheory.Category.Cat.Limit

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured
open CategoryTheory CategoryTheory.Limits Opposite Silmaril.Logic.Institution
universe u
noncomputable section
variable {Sign : Type u} [Category.{u} Sign]

/-- Structured signatures are varying-shape diagrams of signatures.
Durán–Meseguer (1999), Definition 4.1. -/
abbrev Signature (Sign : Type u) [Category.{u} Sign] := CoDiagram.{u,u} Sign

/-- A sentence retains the node at which it is asserted (Definition 4.2). -/
def Sentence (I : ClassicInstitution.{u,u,u,u,u} Sign) (D : Signature Sign) :=
  (node : D.Sign) × I.Sen.obj (D.I.obj node)

/-- Contravariant diagram of local model categories. -/
def modelDiagram (I : ClassicInstitution.{u,u,u,u,u} Sign) (D : Signature Sign) :
    D.Signᵒᵖ ⥤ Cat.{u,u} := D.I.op ⋙ I.Mod

/-- Compatible families of local models and compatible families of model maps.
This is the strict limit-category construction of Definition 4.3, including
morphisms; it is not the product of independent node models. -/
def Models (I : ClassicInstitution.{u,u,u,u,u} Sign) (D : Signature Sign) : Cat.{u,u} :=
  Cat.HasLimits.limitConeX (modelDiagram I D)

/-- Projection of a compatible model family to one node. -/
def projection (I : ClassicInstitution.{u,u,u,u,u} Sign) (D : Signature Sign) (node : D.Sign) :
    Models I D ⟶ I.Mod.obj (op (D.I.obj node)) :=
  (Cat.HasLimits.limitCone (modelDiagram I D)).π.app (op node)

/-- A structured model satisfies a tagged sentence at its tagged node
(Definition 4.5). -/
def Sat (I : ClassicInstitution.{u,u,u,u,u} Sign) (D : Signature Sign)
    (M : Models I D) (φ : Sentence I D) : Prop :=
  I.Sat (D.I.obj φ.1) ((projection I D φ.1).toFunctor.obj M) φ.2


/-- Node-tagged sentence translation along a structured signature map. -/
def sentenceMap (I : ClassicInstitution.{u,u,u,u,u} Sign) {D E : Signature Sign}
    (f : D ⟶ E) (φ : Sentence I D) : Sentence I E :=
  ⟨f.Φ.obj φ.1, I.Sen.map (f.ρ.app φ.1) φ.2⟩

/-- The reduct cone: select the translated node and reduce along its signature map. -/
def reductCone (I : ClassicInstitution.{u,u,u,u,u} Sign) {D E : Signature Sign}
    (f : D ⟶ E) : Cone (modelDiagram I D) where
  pt := Models I E
  π := {
    app := fun node => projection I E (f.Φ.obj node.unop) ≫ I.Mod.map (f.ρ.app node.unop).op
    naturality := by
      intro i j g
      have hρ := f.ρ.naturality g.unop
      have hπ := (Cat.HasLimits.limitCone (modelDiagram I E)).π.naturality (f.Φ.map g.unop).op
      dsimp [modelDiagram] at hπ ⊢
      simp only [Category.assoc]
      rw [← I.Mod.map_comp, ← op_comp]
      rw [hρ, op_comp, I.Mod.map_comp]
      simpa only [projection, Models, modelDiagram, Functor.comp_map, Category.assoc, Cat.HasLimits.limitCone] using
        congrArg (fun k => k ≫ I.Mod.map (f.ρ.app j.unop).op) hπ }

/-- Model reduct along a structured signature map (Definition 4.4). -/
def reduct (I : ClassicInstitution.{u,u,u,u,u} Sign) {D E : Signature Sign}
    (f : D ⟶ E) : Models I E ⟶ Models I D :=
  Cat.HasLimits.limitConeLift (modelDiagram I D) (reductCone I f)

end
end Silmaril.Logic.Institution.Structured
