module

public import Silmaril.Logic.ITree.Institution.Trace.Category.Defs

public section

namespace Silmaril.Logic.ITree.TraceInstitution.Proofs

open CategoryTheory Silmaril.Elgot.ITree

universe u v w

theorem restrictLiftInstitution :
    TraceSignature.includeInjectiveRequests.{u} ⋙ liftInstitution.{u,v,w}.toRoomFunctor =
      institution.{u,v,w}.toRoomFunctor := by
  refine Functor.ext
    (F := TraceSignature.includeInjectiveRequests.{u} ⋙ liftInstitution.{u,v,w}.toRoomFunctor)
    (G := institution.{u,v,w}.toRoomFunctor) (fun _ => rfl) ?_
  intro S T f
  change liftInstitution.{u,v,w}.corridor (TraceSignature.includeInjectiveRequests.map f) =
    𝟙 (institution.{u,v,w}.room S) ≫ institution.{u,v,w}.corridor f ≫ 𝟙 (institution.{u,v,w}.room T)
  have same : liftInstitution.{u,v,w}.corridor (TraceSignature.includeInjectiveRequests.map f) =
      institution.{u,v,w}.corridor f :=
    Silmaril.Logic.Institution.Room.hom_ext (funext fun φ => φ.translateLift_eq f) rfl
  exact same.trans ((Category.id_comp (institution.{u,v,w}.corridor f ≫ 𝟙 _)).trans
    (Category.comp_id _)).symm

end Silmaril.Logic.ITree.TraceInstitution.Proofs
