module

public import Silmaril.Logic.Institution.Structured.Theories.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured
open CategoryTheory CategoryTheory.Limits Opposite Silmaril.Logic.Institution
universe u
noncomputable section
variable {Sign : Type u} [Category.{u} Sign]

/-- Compatibility of a family at a diagram edge, including the underlying functors. -/
theorem projection_edge (I : ClassicInstitution.{u,u,u,u,u} Sign) (D : Signature Sign)
    {i j : D.Sign} (f : i ⟶ j) :
    projection I D j ≫ I.Mod.map (D.I.map f).op = projection I D i := by
  have h := (Cat.HasLimits.limitCone (modelDiagram I D)).π.naturality f.op
  simpa only [modelDiagram, Functor.comp_map, Functor.op_map, Functor.const_obj_map,
    projection, Models, Cat.HasLimits.limitCone, Functor.const_obj_obj,
    Quiver.Hom.unop_op, Category.id_comp] using h.symm

/-- Nodewise consequences are stable under diagram edges because model families
are compatible; this is stronger than a statement about independent local models. -/
theorem nodeConsequences_edge (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) {i j : P.sig.Sign} (f : i ⟶ j)
    {φ : I.Sen.obj (P.sig.I.obj i)} (hφ : φ ∈ nodeConsequences I P i) :
    I.Sen.map (P.sig.I.map f) φ ∈ nodeConsequences I P j := by
  intro M hM
  have hi := hφ M hM
  have heq := congrArg (fun k => k.toFunctor.obj M) (projection_edge I P.sig f)
  change I.Sat _ _ (I.Sen.map (P.sig.I.map f) φ)
  rw [I.satisfaction]
  exact heq.symm ▸ hi

/-- The actual node consequence set is semantically closed. -/
theorem nodeConsequences_closed (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) (node : P.sig.Sign) :
    (I.toRoomFunctor.obj (P.sig.I.obj node)).closure (nodeConsequences I P node) =
      nodeConsequences I P node := by
  apply Set.Subset.antisymm
  · intro φ hφ M hM
    exact hφ ((projection I P.sig node).toFunctor.obj M) (fun ψ hψ => hψ M hM)
  · exact (I.toRoomFunctor.obj _).subset_closure _

/-- Diagram of complete local consequences of a structured presentation. -/
def consequenceDiagram (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I) :
    CoDiagram.{u,u} (Spec I.toRoomFunctor) where
  Sign := P.sig.Sign
  I := {
    obj := nodeTheory I P
    map := fun f => ⟨P.sig.I.map f, fun _ hφ =>
      (I.toRoomFunctor.obj _).subset_closure _ (nodeConsequences_edge I P f hφ)⟩
    map_id := fun _ => Spec.hom_ext (P.sig.I.map_id _)
    map_comp := fun f g => Spec.hom_ext (P.sig.I.map_comp f g) }

/-- A structured semantic map transports all node consequences. -/
theorem nodeConsequences_map (I : ClassicInstitution.{u,u,u,u,u} Sign)
    {P Q : StructuredTheory I} (f : P ⟶ Q) (node : P.sig.Sign)
    {φ : I.Sen.obj (P.sig.I.obj node)} (hφ : φ ∈ nodeConsequences I P node) :
    I.Sen.map (f.sig.ρ.app node) φ ∈ nodeConsequences I Q (f.sig.Φ.obj node) := by
  exact (Theory.presentation_lemma f.sig P.axioms Q.axioms).2 f.mapsTo hφ

/-- Paper J sends a structured presentation to its diagram of local consequences. -/
def J (I : ClassicInstitution.{u,u,u,u,u} Sign) :
    StructuredTheory I ⥤ CoDiagram.{u,u} (Spec I.toRoomFunctor) where
  obj := consequenceDiagram I
  map f := {
    Φ := f.sig.Φ
    ρ := {
      app := fun node => ⟨f.sig.ρ.app node, fun _ hφ =>
        (I.toRoomFunctor.obj _).subset_closure _ (nodeConsequences_map I f node hφ)⟩
      naturality := fun _ _ g => Spec.hom_ext (f.sig.ρ.naturality g) } }
  map_id _ := rfl
  map_comp _ _ := rfl


/-- A diagram map induces a map between the unions of node-tagged axioms. -/
def unionMap (I : ClassicInstitution.{u,u,u,u,u} Sign)
    {D E : CoDiagram.{u,u} (Spec I.toRoomFunctor)} (f : D ⟶ E) :
    unionTheory I D ⟶ unionTheory I E where
  sig := {
    Φ := f.Φ
    ρ := {
      app := fun node => (f.ρ.app node).sig
      naturality := fun _ _ g => congrArg Spec.Hom.sig (f.ρ.naturality g) } }
  mapsTo := by
    intro φ hφ M hM
    exact (f.ρ.app φ.1).mapsTo hφ
      ((projection I (diagramSignature I E) (f.Φ.obj φ.1)).toFunctor.obj M)
      (fun ψ hψ => hM ⟨f.Φ.obj φ.1, ψ⟩ hψ)

/-- Paper R assembles local axioms into one structured presentation. -/
def R (I : ClassicInstitution.{u,u,u,u,u} Sign) :
    CoDiagram.{u,u} (Spec I.toRoomFunctor) ⥤ StructuredTheory I where
  obj := unionTheory I
  map := unionMap I
  map_id _ := rfl
  map_comp _ _ := rfl

end
end Silmaril.Logic.Institution.Structured
