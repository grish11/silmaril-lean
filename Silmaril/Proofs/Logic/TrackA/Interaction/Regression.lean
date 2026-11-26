module

import Silmaril.Logic.TrackA.Interaction.Thms
import Silmaril.Semantics.TrackA.Interaction.Elgot.Thms

namespace Silmaril.Logic.TrackA.Interaction.Regression

open CategoryTheory Opposite Silmaril.Semantics.TrackA.Interaction

private abbrev Protocol : TraceSignature := ⟨⟨Bool, fun _ => Unit⟩⟩

private def mergeRequests : Protocol ⟶ Protocol :=
  ⟨⟨fun _ => false, fun _ r => r⟩, fun _ => Function.bijective_id⟩

private def actions : Forest Protocol.signature Signature.noChoice (Option Bool) Bool where
  State := Bool ⊕ Bool
  unfold
    | .inl q => .vis q fun _ => .inr q
    | .inr q => .ret (if q then some true else none)
  root := Sum.inl

private theorem returnedAfter (q : Bool) :
    Trace.finite [⟨q, ()⟩] (.returned (if q then some true else none)) ∈ actions.observes :=
  ⟨q, .inr q, .inr q, .cons ⟨.inl q, .refl,
    .vis (c := actions.unfold) (q := q) (next := fun _ => .inr q) rfl ()⟩ (.nil _), .refl, rfl⟩

example : some (Trace.finite [⟨false, ()⟩] (.returned true)) ∈
    (actions.relabel mergeRequests.hom).toExplicit := by
  rw [Forest.toExplicit_relabel]
  refine ⟨some (Trace.finite [⟨true, ()⟩] (.returned true)),
    ⟨Trace.finite [⟨true, ()⟩] (.returned (some true)), returnedAfter true, rfl⟩, ?_⟩
  have reply : mergeRequests.reply true () = () := Subsingleton.elim _ _
  change some (Trace.finite (S := Protocol.signature) [⟨false, mergeRequests.reply true ()⟩] (.returned true)) = _
  rw [reply]

example : (actions.relabel mergeRequests.hom).toCatastrophic = ⊤ := by
  apply (Forest.toCatastrophic_eq_top_iff _).mpr
  rw [Forest.toExplicit_relabel]
  exact ⟨none, ⟨Trace.finite [⟨false, ()⟩] (.returned none), returnedAfter false, rfl⟩, rfl⟩

example (bound : Set (Trace Protocol.signature (Option Bool))) :
    (treeInstitution Signature.noChoice (Option Bool) Bool).Sat (op Protocol) (Discrete.mk actions)
      ((treeInstitution Signature.noChoice (Option Bool) Bool).Sen.map mergeRequests.op bound) ↔
    (treeInstitution Signature.noChoice (Option Bool) Bool).Sat (op Protocol)
      (Discrete.mk (actions.relabel mergeRequests.hom)) bound :=
  (treeInstitution Signature.noChoice (Option Bool) Bool).satisfaction mergeRequests.op _ _

private abbrev NoReply : Signature := ⟨Bool, fun _ => Empty⟩

private def discardReplies : Signature.Hom Protocol.signature NoReply := ⟨id, fun _ r => r.elim⟩

private def requestLoop : Coalgebra Protocol.signature Signature.noChoice Unit Unit :=
  fun _ => .vis false fun _ => ()

/-- A general dependent morphism can introduce stuckness by deleting all replies. -/
example :
    Trace.finite [] (.stuck false) ∈ (requestLoop.relabel discardReplies).observes () ∧
      ¬ requestLoop.EndsAt () (.stuck false) :=
  ⟨⟨(), (), .nil _, .refl, ⟨inferInstance, fun r => r.elim, rfl⟩⟩,
    fun ends => ends.1.false ()⟩

/-- A single infinite state path changes the visible request at each step. -/
example : Trace.infinite (fun n => (⟨n % 2 == 1, ()⟩ : Protocol.signature.Exchange)) ∈
    (WeakITree.toDelayed (Elgot.guardedLoop (S := Protocol.signature) (A := Unit)
      (fun n : Nat => n % 2 == 1) (fun n _ => .inr (n + 1)) 0)).observes :=
  Elgot.loop_observes_infinite (S := Protocol.signature) _ _ id (fun _ => ()) (fun _ => rfl)

end Silmaril.Logic.TrackA.Interaction.Regression
