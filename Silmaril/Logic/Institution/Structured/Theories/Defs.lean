module

public import Silmaril.Logic.Institution.Structured.Thms
public import Silmaril.Logic.Institution.Theory

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured
open CategoryTheory CategoryTheory.Limits Opposite Silmaril.Logic.Institution
universe u
noncomputable section
variable {Sign : Type u} [Category.{u} Sign]

/-- Structured theory presentations use semantic-consequence morphisms. -/
abbrev StructuredTheory (I : ClassicInstitution.{u,u,u,u,u} Sign) := Spec (institution I)

/-- All consequences visible at one node, computed from actual compatible
models of the complete structured presentation (the object part of paper J). -/
def nodeConsequences (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) (node : P.sig.Sign) : Set (I.Sen.obj (P.sig.I.obj node)) :=
  {φ | ⟨node, φ⟩ ∈ (room I P.sig).closure P.axioms}

/-- Underlying structured signature of a diagram of semantic presentations. -/
def diagramSignature (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (D : CoDiagram.{u,u} (Spec I.toRoomFunctor)) : Signature Sign :=
  ⟨D.Sign, D.I ⋙ Spec.forget I.toRoomFunctor⟩

/-- Union of node-tagged axioms (the object part of paper R). -/
def unionTheory (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (D : CoDiagram.{u,u} (Spec I.toRoomFunctor)) : StructuredTheory I :=
  ⟨diagramSignature I D, {φ : Sentence I (diagramSignature I D) | φ.2 ∈ (D.I.obj φ.1).axioms}⟩

/-- The local presentation at one node of a structured theory. -/
def nodeTheory (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I)
    (node : P.sig.Sign) : Spec I.toRoomFunctor :=
  ⟨P.sig.I.obj node, nodeConsequences I P node⟩

end
end Silmaril.Logic.Institution.Structured
