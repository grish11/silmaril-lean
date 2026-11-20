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
