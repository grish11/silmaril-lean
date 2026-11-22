module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

open Silmaril.Wasm.Component.Runtime

/-- A successful registration publishes the tree and both claim classes together. -/
theorem register_claims {sig : Signature} {state registered : State sig} {tree : Tree sig}
    (success : state.register tree = .ok registered) :
    registered.accepted = tree :: state.accepted ∧
      registered.held = rootReceipts tree ++ state.held ∧
      registered.endpoints = rootEndpoints tree ++ state.endpoints :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.register_claims success

/-- Equal reached conflict tests and allocation indices give the same alias
decision or handle, without identifying the two updated writers. -/
theorem register_observations {sig : Signature} {left right : State sig} {tree : Tree sig}
    (agrees : left.RegistrationChecksAgree right tree)
    (length : left.accepted.length = right.accepted.length) :
    (left.register tree).map (fun writer => writer.accepted.length) =
      (right.register tree).map (fun writer => writer.accepted.length) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.register_observations agrees length

/-- A one-sided owner spend does not change conflicts for a historically
accepted owner. A one-sided endpoint spend frames probes disjoint from it. -/
theorem State.RegistrationChecksAgree.left_spend {sig : Signature} {left right : State sig} {tree : Tree sig}
    (agrees : left.RegistrationChecksAgree right tree) (update : Spend)
    (frames : update.FramesRegistration left tree) :
    (update.apply left).RegistrationChecksAgree right tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.registration_after_left_spend agrees update frames

/-- A prepare probe observes the raw writer, but only at its nominal arena identity. -/
theorem Spend.prepare_observation_agrees {sig : Signature} {left right : State sig} (update : Spend)
    (resource : RtId) (id : HandleObjId) (agrees : left.ownerObservation id = right.ownerObservation id)
    (frames : ∀ spent, update = .owner spent → id ≠ spent) :
    ((update.apply left).prepare resource id).map Prod.fst = (right.prepare resource id).map Prod.fst :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.prepare_after_left_spend update resource id agrees frames

theorem Spend.ObservationAgrees.spend {sig : Signature} {left right : State sig} {probe : Spend}
    (agrees : probe.ObservationAgrees left right) (update : Spend) :
    probe.ObservationAgrees (update.apply left) (update.apply right) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.observation_after_spend agrees update

theorem Spend.ObservationAgrees.left_spend {sig : Signature} {left right : State sig} {probe : Spend}
    (agrees : probe.ObservationAgrees left right) (update : Spend) (distinct : probe ≠ update) :
    probe.ObservationAgrees (update.apply left) right :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.observation_after_left_spend agrees update distinct

theorem State.LiveClaimsAgree.observe {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) (probe : Spend) : probe.ObservationAgrees left right := by
  cases probe with | owner id => exact agrees.owners id | endpoint id => exact agrees.endpoints id

theorem State.prepare_observation_eq {sig : Signature} {left right : State sig}
    (resource : RtId) (id : HandleObjId) (agrees : left.ownerObservation id = right.ownerObservation id) :
    (left.prepare resource id).map Prod.fst = (right.prepare resource id).map Prod.fst :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.prepare_observation_eq resource id agrees

theorem State.IndexedClaimsAgree.registration {sig : Signature} {left right : State sig}
    (agrees : left.IndexedClaimsAgree right) (tree : Tree sig) : left.RegistrationChecksAgree right tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.indexedClaims_registration agrees tree

theorem State.IndexedClaimsAgree.spend {sig : Signature} {left right : State sig}
    (agrees : left.IndexedClaimsAgree right) (update : Spend) :
    (update.apply left).IndexedClaimsAgree (update.apply right) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.indexedClaims_spend agrees update

theorem State.IndexedClaimsAgree.register {sig : Signature} {left right : State sig}
    (agrees : left.IndexedClaimsAgree right) (tree : Tree sig) :
    (∃ issue, left.register tree = .error issue ∧ right.register tree = .error issue) ∨
      ∃ lhs rhs, left.register tree = .ok lhs ∧ right.register tree = .ok rhs ∧ lhs.IndexedClaimsAgree rhs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.indexedClaims_register agrees tree

theorem State.LiveClaimsAgree.toIndexed {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) : left.IndexedClaimsAgree right :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.liveClaims_indexed agrees

theorem State.LiveClaimsAgree.spend {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) (update : Spend) :
    (update.apply left).LiveClaimsAgree (update.apply right) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.liveClaims_spend agrees update

theorem State.LiveClaimsAgree.prepare {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) (resource : RtId) (id : HandleObjId) :
    (left.prepare resource id).map Prod.fst = (right.prepare resource id).map Prod.fst :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.liveClaims_prepare agrees resource id

theorem Spend.not_live {sig : Signature} (update : Spend) (state : State sig) : ¬ update.Live (update.apply state) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.spend_not_live update state

/-- A checked-only spend can be compared to a projection of the canonical
writer, but not to the unchanged writer consulted by a subsequent real read. -/
theorem State.LiveClaimsAgree.asymmetricSpend {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) {update : Spend} (live : update.Live left) :
    (update.apply left).LiveClaimsAgree (update.apply right) ∧ ¬ (update.apply left).LiveClaimsAgree right :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.liveClaims_asymmetricSpend agrees live

theorem State.LiveClaimsAgree.prepare_success {sig : Signature} {left right next : State sig}
    (agrees : left.LiveClaimsAgree right) {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : left.prepare resource id = .ok (representation, next)) :
    ∃ peer, right.prepare resource id = .ok (representation, peer) ∧ next.LiveClaimsAgree peer :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.liveClaims_prepare_success agrees success

theorem State.LiveClaimsAgree.register {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) (tree : Tree sig) :
    (∃ issue, left.register tree = .error issue ∧ right.register tree = .error issue) ∨
      ∃ lhs rhs, left.register tree = .ok lhs ∧ right.register tree = .ok rhs ∧ lhs.LiveClaimsAgree rhs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.liveClaims_register agrees tree

/-- Even equal live owner membership cannot determine a nominal prepare observation. -/
theorem indexed_not_owner_observations {sig : Signature} (resource : RtId) (identity : HandleObjId)
    {rep other : Nat} (different : rep ≠ other) :
    ∃ left right : State sig, left.IndexedClaimsAgree right ∧
      (left.prepare resource identity).map Prod.fst ≠ (right.prepare resource identity).map Prod.fst :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.indexed_not_owner_observations resource identity different

/-- Equal accepted indices do not imply equal registration decisions: a
real spend releases a live endpoint without removing the observed root. -/
theorem accepted_not_endpoint_conflicts {sig : Signature} {tree : Tree sig} {id : EndId}
    (unowned : rootReceipts tree = []) (one : rootEndpoints tree = [id]) :
    ∃ first second spent : State sig, ({} : State sig).register tree = .ok first ∧
      spent = (Spend.endpoint id).apply first ∧ first.accepted = spent.accepted ∧
      first.register tree = .error .alias ∧ spent.register tree = .ok second :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.accepted_not_endpoint_conflicts unowned one

theorem register_retains_retirement {sig : Signature} {state registered : State sig}
    {tree : Tree sig} {id : HandleObjId}
    (success : state.register tree = .ok registered) (retired : state.retiredOwner id) :
    registered.retiredOwner id :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.register_retains_retirement success retired

theorem prepare_preserves_endpoints {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) :
    spent.endpoints = state.endpoints :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.prepare_preserves_endpoints success

/-- The nominal resource type, arena identity and representation all come from the
same held receipt. An accepted observation alone cannot authorize either operation. -/
theorem prepare_provenance {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) :
    ∃ receipt ∈ state.held,
      receiptId receipt = id ∧ receipt.1 = resource ∧ receipt.2.representation = representation :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.prepare_provenance success

/-- Committing a prepared operation spends just the selected identity, not any other
owner at the same representation, and never removes an accepted observation. -/
theorem prepare_spends {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) :
    spent.accepted = state.accepted ∧
      ∀ receipt, receipt ∈ spent.held ↔ receipt ∈ state.held ∧ receiptId receipt ≠ id :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.prepare_spends success

/-- In the committed state, repeating a give or drop for that identity is a typed refusal,
even when the caller asks for a different nominal resource type. -/
theorem prepare_no_repeat {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) (other : RtId) :
    spent.prepare other id = .error .unclaimed :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.prepare_no_repeat success other

theorem spendEndpoint_preserves_owners {sig : Signature} {state spent : State sig} {id : EndId}
    (success : state.spendEndpoint id = .ok spent) :
    spent.accepted = state.accepted ∧ spent.held = state.held ∧ id ∉ spent.endpoints := by
  unfold State.spendEndpoint at success
  split at success <;> cases success
  simp [Spend.apply]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
