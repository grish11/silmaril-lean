module

public import Silmaril.Logic.ITree.Institution.Trace.Category.Defs
import Silmaril.Proofs.Logic.ITree.Institution.Trace.Category

@[expose] public section

namespace Silmaril.Logic.ITree.TraceInstitution

open CategoryTheory Silmaril.Elgot.ITree

universe u v w

/-- Restriction along the original bijective-reply arrows recovers the
original institution as an equality of room functors. This fixes the
sentence and model types, both maps on arrows, and satisfaction. -/
theorem restrictLiftInstitution :
    TraceSignature.includeInjectiveRequests.{u} ⋙ liftInstitution.{u,v,w}.toRoomFunctor =
      institution.{u,v,w}.toRoomFunctor :=
  Proofs.restrictLiftInstitution

end Silmaril.Logic.ITree.TraceInstitution
