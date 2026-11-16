module

public import Silmaril.Logic.Institution.Structured.Constraints.Institution

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured.Constraints
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution
universe u
noncomputable section
variable {Sign : Type u} [Category.{u} Sign] (I : ClassicInstitution.{u,u,u,u,u} Sign)

/-- `S(C(I))`: constraints are attached to individual diagram nodes
(Durán–Meseguer 1999, Definition 4.15). -/
def localInstitution : Signature Sign ⥤ Room.{u,u,u} :=
  Structured.institution (ClassicInstitution.ofRoomFunctor (institution I.toRoomFunctor))

/-- `C(S(I))`: constraints relate structured theories as wholes (§4.3).
The pointwise formulation permits this construction without first choosing
left adjoints; Theorem 4.13 supplies those under the paper's assumptions. -/
def globalInstitution : Signature Sign ⥤ Room.{u+1,u,u} :=
  institution (Structured.institution I)

/-- A local sentence retains its node; a local constraint only mentions
original theory maps and a context map into that node's signature. -/
def localSentenceEquiv (D : Signature Sign) :
    ((localInstitution I).obj D).Sen ≃
      ((node : D.Sign) × ((I.Sen.obj (D.I.obj node)) ⊕ Constraint I.toRoomFunctor (D.I.obj node))) :=
  Equiv.refl _

/-- A global constraint instead mentions semantic maps between structured
theories and a context map into the entire structured signature. -/
def globalSentenceEquiv (D : Signature Sign) :
    ((globalInstitution I).obj D).Sen ≃
      Sentence I D ⊕ Constraint (Structured.institution I) D := Equiv.refl _

/-- Both constructions retain the same compatible model families. -/
theorem local_global_models (D : Signature Sign) :
    ((localInstitution I).obj D).Mod = ((globalInstitution I).obj D).Mod := by
  rfl

/-- Both constructions use the same reduct functors on compatible models. -/
theorem local_global_reduct {D E : Signature Sign} (f : D ⟶ E) :
    ((localInstitution I).map f).mod = ((globalInstitution I).map f).mod := by
  rfl

/-- Node-local constrained theories inherit cocompleteness from the original
signature category (the final colimit assertion of §4.3). -/
theorem local_theories_hasColimits [HasColimitsOfSize.{u,u} Sign] :
    HasColimitsOfSize.{u,u} (Spec (localInstitution I)) :=
  structured_hasColimits_of_signatures
    (ClassicInstitution.ofRoomFunctor (institution I.toRoomFunctor))

/-- Globally constrained structured theories also inherit cocompleteness from
original signatures (the final colimit assertion of §4.3). -/
theorem global_theories_hasColimits [HasColimitsOfSize.{u,u} Sign] :
    HasColimitsOfSize.{u,u} (Spec (globalInstitution I)) := by
  have : HasColimitsOfSize.{u,u} (Signature Sign) := signature_hasColimits
  exact ⟨fun K _ => spec_hasColimitsOfShape (globalInstitution I) K⟩

end
end Silmaril.Logic.Institution.Structured.Constraints
