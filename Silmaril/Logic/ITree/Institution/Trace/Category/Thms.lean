module

public import Silmaril.Logic.ITree.Institution.Trace.Category.Defs
import Silmaril.Proofs.Logic.ITree.Institution.Trace.Category

@[expose] public section

namespace Silmaril.Logic.ITree.TraceInstitution

open CategoryTheory Silmaril.Elgot.ITree

universe u v w

/-- Validity in the wider institution is detected by its all-replies model. -/
theorem liftInstitution_valid_iff (T : Signature.InjectiveRequests.{u})
    (φ : liftInstitution.{u,v,0}.Sen.obj T) :
    (∀ M : liftInstitution.{u,v,0}.Mod.obj (Opposite.op T), liftInstitution.{u,v,0}.Sat T M φ) ↔
      Sat (allRepliesModel ⟨T.obj⟩) φ :=
  ⟨fun valid => valid ⟨allRepliesModel ⟨T.obj⟩⟩,
    fun sat M => (valid_iff_sat_allReplies (S := ⟨T.obj⟩) φ).mpr sat M.as⟩

/-- Restriction along the original bijective-reply arrows recovers the
original institution as an equality of room functors. This fixes the
sentence and model types, both maps on arrows, and satisfaction. -/
theorem restrictLiftInstitution :
    TraceSignature.includeInjectiveRequests.{u} ⋙ liftInstitution.{u,v,w}.toRoomFunctor =
      institution.{u,v,w}.toRoomFunctor :=
  Proofs.restrictLiftInstitution

end Silmaril.Logic.ITree.TraceInstitution
