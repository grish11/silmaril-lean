module

public import Silmaril.Logic.Institution.Structured.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured
open CategoryTheory CategoryTheory.Limits Opposite Silmaril.Logic.Institution
universe u
noncomputable section
variable {Sign : Type u} [Category.{u} Sign]

@[simp] theorem reduct_projection (I : ClassicInstitution.{u,u,u,u,u} Sign)
    {D E : Signature Sign} (f : D ⟶ E) (node : D.Sign) :
    reduct I f ≫ projection I D node =
      projection I E (f.Φ.obj node) ≫ I.Mod.map (f.ρ.app node).op := by
  exact (Cat.HasLimits.limitConeIsLimit (modelDiagram I D)).fac (reductCone I f) (op node)

theorem model_hom_ext (I : ClassicInstitution.{u,u,u,u,u} Sign) (D : Signature Sign)
    {X : Cat.{u,u}} {f g : X ⟶ Models I D}
    (h : ∀ node, f ≫ projection I D node = g ≫ projection I D node) : f = g := by
  apply (Cat.HasLimits.limitConeIsLimit (modelDiagram I D)).hom_ext
  intro node
  exact h node.unop

@[simp] theorem reduct_id (I : ClassicInstitution.{u,u,u,u,u} Sign) (D : Signature Sign) :
    reduct I (𝟙 D) = 𝟙 (Models I D) := by
  apply model_hom_ext I D
  intro node
  rw [reduct_projection]
  change projection I D node ≫ I.Mod.map (𝟙 _) = 𝟙 _ ≫ projection I D node
  rw [Functor.map_id, Category.comp_id, Category.id_comp]


@[simp] theorem reduct_comp (I : ClassicInstitution.{u,u,u,u,u} Sign)
    {D E F : Signature Sign} (f : D ⟶ E) (g : E ⟶ F) :
    reduct I (f ≫ g) = reduct I g ≫ reduct I f := by
  apply model_hom_ext I D
  intro node
  rw [reduct_projection, Category.assoc, reduct_projection]
  simp only [CoDiagram.comp_app, op_comp, Functor.map_comp]
  change projection I F (g.Φ.obj (f.Φ.obj node)) ≫ _ ≫ _ = _
  exact (congrArg (fun k => k ≫ I.Mod.map (f.ρ.app node).op)
    (reduct_projection I g (f.Φ.obj node))).symm


/-- Tagged sentences form a functor (Definition 4.2). -/
def sentenceFunctor (I : ClassicInstitution.{u,u,u,u,u} Sign) :
    Signature Sign ⥤ Type u where
  obj := Sentence I
  map {D E} f := ↾(sentenceMap I f)
  map_id D := by
    ext φ
    rcases φ with ⟨node, φ⟩
    change (⟨node, I.Sen.map (𝟙 _) φ⟩ : Sentence I D) = ⟨node, φ⟩
    exact congrArg (fun ψ => (⟨node, ψ⟩ : Sentence I D)) (I.Sen.map_id_apply _ φ)
  map_comp f g := by
    ext φ
    rcases φ with ⟨node, φ⟩
    change sentenceMap I (f ≫ g) ⟨node, φ⟩ =
      sentenceMap I g (sentenceMap I f ⟨node, φ⟩)
    simp only [sentenceMap, CoDiagram.comp_app, I.Sen.map_comp_apply]
    rfl


/-- Nodewise truth is preserved by structured signature translation
(Proposition 4.6). -/
theorem satisfaction (I : ClassicInstitution.{u,u,u,u,u} Sign)
    {D E : Signature Sign} (f : D ⟶ E) (M : Models I E) (φ : Sentence I D) :
    Sat I E M (sentenceMap I f φ) ↔ Sat I D ((reduct I f).toFunctor.obj M) φ := by
  have hprojection := congrArg (fun k => k.toFunctor.obj M) (reduct_projection I f φ.1)
  change I.Sat _ _ (I.Sen.map (f.ρ.app φ.1) φ.2) ↔ I.Sat _ _ φ.2
  rw [I.satisfaction]
  exact iff_of_eq (congrArg (fun value => I.Sat _ value φ.2) hprojection.symm)

/-- The room at a structured signature. -/
def room (I : ClassicInstitution.{u,u,u,u,u} Sign) (D : Signature Sign) : Room.{u,u,u} :=
  ⟨Sentence I D, Models I D, Sat I D⟩

/-- The corridor combines tagged sentence translation and compatible-family reduct. -/
def corridor (I : ClassicInstitution.{u,u,u,u,u} Sign) {D E : Signature Sign}
    (f : D ⟶ E) : room I D ⟶ room I E :=
  ⟨sentenceMap I f, (reduct I f).toFunctor, satisfaction I f⟩

/-- The structured institution (Definition 4.7). -/
def institution (I : ClassicInstitution.{u,u,u,u,u} Sign) : Signature Sign ⥤ Room.{u,u,u} where
  obj := room I
  map := corridor I
  map_id D := by
    apply Room.hom_ext
    · funext φ
      exact ConcreteCategory.congr_hom ((sentenceFunctor I).map_id D) φ
    · exact congrArg Cat.Hom.toFunctor (reduct_id I D)
  map_comp f g := by
    apply Room.hom_ext
    · funext φ
      exact ConcreteCategory.congr_hom ((sentenceFunctor I).map_comp f g) φ
    · exact congrArg Cat.Hom.toFunctor (reduct_comp I f g)

/-- The separate sentence/model presentation of the same structured institution. -/
def classicInstitution (I : ClassicInstitution.{u,u,u,u,u} Sign) :
    ClassicInstitution (Signature Sign) :=
  ClassicInstitution.ofRoomFunctor (institution I)

end
end Silmaril.Logic.Institution.Structured
