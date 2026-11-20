module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims

open Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

theorem register_claims {sig : Signature} {state registered : State sig}
    {tree : OwnedMemory.Tree sig} (success : state.register tree = .ok registered) :
    registered.accepted = tree :: state.accepted ∧
      registered.held = rootReceipts tree ++ state.held ∧
      registered.endpoints = rootEndpoints tree ++ state.endpoints := by
  unfold State.register at success
  dsimp only at success
  split at success <;> cases success
  exact ⟨rfl, rfl, rfl⟩

theorem register_retains_retirement {sig : Signature} {state registered : State sig}
    {tree : OwnedMemory.Tree sig} {id : HandleObjId}
    (success : state.register tree = .ok registered) (retired : state.retiredOwner id) :
    registered.retiredOwner id := by
  have history := register_claims success
  have fresh : id ∉ (rootReceipts tree).map receiptId := by
    unfold State.register at success
    dsimp only at success
    split at success
    next allowed =>
      intro member
      have known : id ∈ ((state.accepted.flatMap rootReceipts ++ state.held).map receiptId) := by
        simp [retired.1]
      have noneKnown : ((rootReceipts tree).map receiptId).any
          (((state.accepted.flatMap rootReceipts ++ state.held).map receiptId).contains) = false := by
        simpa using allowed.2.1
      have absent := List.any_eq_false.mp noneKnown id member
      rw [List.contains_iff_mem.mpr known] at absent
      contradiction
    next => contradiction
  unfold State.retiredOwner
  rw [history.1, history.2.1]
  simp [retired.1, retired.2, fresh]

theorem prepare_preserves_endpoints {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) :
    spent.endpoints = state.endpoints := by
  unfold State.prepare at success
  split at success
  · contradiction
  · split at success <;> cases success
    rfl

theorem prepare_provenance {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) :
    ∃ receipt ∈ state.held,
      receiptId receipt = id ∧ receipt.1 = resource ∧ receipt.2.representation = representation := by
  unfold State.prepare at success
  split at success
  · contradiction
  next receipt found =>
    split at success
    · contradiction
    next sameType =>
      cases success
      exact ⟨receipt, List.mem_of_find?_eq_some found, by simpa using List.find?_some found,
        by simpa using sameType, rfl⟩

theorem prepare_spends {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) :
    spent.accepted = state.accepted ∧
      ∀ receipt, receipt ∈ spent.held ↔ receipt ∈ state.held ∧ receiptId receipt ≠ id := by
  unfold State.prepare at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · cases success
      exact ⟨rfl, fun _ => by simp [Spend.apply]⟩

theorem prepare_no_repeat {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) (other : RtId) :
    spent.prepare other id = .error .unclaimed := by
  have missing : (spent.held.find? (fun entry => receiptId entry == id)) = none :=
    List.find?_eq_none.mpr fun receipt member => by
      have different := ((prepare_spends success).2 receipt |>.mp member).2
      simp [different]
  simp only [State.prepare, missing]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims
