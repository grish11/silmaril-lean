module

public import Silmaril.Logic.Institution.Structured.Theories.Adjunction
public import Silmaril.Logic.Institution.Structured.DiagramColimits
public import Silmaril.Logic.Institution.Colimits
public import Mathlib.CategoryTheory.Monad.Limits

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution
universe u v w a b s p q
noncomputable section
variable {Sign : Type u} [Category.{u} Sign]

/-- The paper's semantic-presentation category has every colimit shape available
in signatures. This transports the existing closed-theory theorem through the
proved specification/theory equivalence (Theorem 4.10). -/
theorem spec_hasColimitsOfShape {C : Type a} [Category.{b} C]
    (I : C ⥤ Room.{s,p,q})
    (K : Type v) [Category.{w} K] [HasColimitsOfShape K C] :
    HasColimitsOfShape K (Spec I) := by
  have : HasColimitsOfShape K (Theory I) := Theory.hasColimitsOfShape
  exact Adjunction.hasColimitsOfShape_of_equivalence (Spec.closure I)

/-- The signature-forgetful functor preserves these colimits, in precisely the
paper's semantic-presentation category (Theorem 4.10). -/
theorem spec_forget_preservesColimitsOfShape {C : Type a} [Category.{b} C]
    (I : C ⥤ Room.{s,p,q})
    (K : Type v) [Category.{w} K] [HasColimitsOfShape K C] :
    PreservesColimitsOfShape K (Spec.forget I) := by
  have : PreservesColimitsOfShape K (Theory.forget I) := Theory.preservesColimitsOfShape
  change PreservesColimitsOfShape K (Spec.closure I ⋙ Theory.forget I)
  infer_instance

/-- The proved right adjoint is a reflective embedding. -/
instance J_reflective (I : ClassicInstitution.{u,u,u,u,u} Sign) : Reflective (J I) := by
  have := (J_fullyFaithful I).full
  have := (J_fullyFaithful I).faithful
  exact { L := R I, adj := theoryAdjunction I }

/-- Reflect a colimit of diagrams of theories to a colimit of structured
presentations. This is the reflective step used in Theorem 4.12; it does not
assume the conclusion that structured theories have colimits. -/
theorem structured_hasColimitsOfShape_of_diagramTheories
    (I : ClassicInstitution.{u,u,u,u,u} Sign) (K : Type v) [Category.{w} K]
    [HasColimitsOfShape K (CoDiagram.{u,u} (Spec I.toRoomFunctor))] :
    HasColimitsOfShape K (StructuredTheory I) :=
  hasColimitsOfShape_of_reflective (J I)

/-- The signature-side route to structured-theory colimits. Together with a
varying-diagram colimit theorem this yields Corollary 4.11. -/
theorem structured_hasColimitsOfShape_of_signatureDiagrams
    (I : ClassicInstitution.{u,u,u,u,u} Sign) (K : Type v) [Category.{w} K]
    [HasColimitsOfShape K (Signature Sign)] :
    HasColimitsOfShape K (StructuredTheory I) :=
  spec_hasColimitsOfShape (institution I) K

/-- Structured signatures inherit small colimits from the original signatures
(Durán–Meseguer 1999, Theorem 4.9). -/
theorem signature_hasColimits [HasColimitsOfSize.{u,u} Sign] :
    HasColimitsOfSize.{u,u} (Signature Sign) := inferInstance

/-- Structured theories inherit small colimits from original signatures
(Durán–Meseguer 1999, Corollary 4.11). -/
theorem structured_hasColimits_of_signatures
    (I : ClassicInstitution.{u,u,u,u,u} Sign) [HasColimitsOfSize.{u,u} Sign] :
    HasColimitsOfSize.{u,u} (StructuredTheory I) := by
  have : HasColimitsOfSize.{u,u} (Signature Sign) := signature_hasColimits
  exact ⟨fun K _ => structured_hasColimitsOfShape_of_signatureDiagrams I K⟩

/-- The structured signature-forgetful functor preserves the resulting colimits
(Durán–Meseguer 1999, Corollary 4.11). -/
theorem structured_forget_preservesColimits
    (I : ClassicInstitution.{u,u,u,u,u} Sign) [HasColimitsOfSize.{u,u} Sign] :
    PreservesColimitsOfSize.{u,u} (Spec.forget (institution I)) := by
  have : HasColimitsOfSize.{u,u} (Signature Sign) := signature_hasColimits
  exact ⟨fun {K} _ => spec_forget_preservesColimitsOfShape (institution I) K⟩

/-- Original theory colimits suffice even without colimits of original
signatures (Durán–Meseguer 1999, Theorem 4.12). -/
theorem structured_hasColimits_of_theories
    (I : ClassicInstitution.{u,u,u,u,u} Sign)
    [HasColimitsOfSize.{u,u} (Spec I.toRoomFunctor)] :
    HasColimitsOfSize.{u,u} (StructuredTheory I) :=
  ⟨fun K _ => structured_hasColimitsOfShape_of_diagramTheories I K⟩

end
end Silmaril.Logic.Institution.Structured
