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

private theorem containsAny_eq {α : Type} [BEq α] [LawfulBEq α] {demands left right : List α}
    (agrees : ∀ id ∈ demands, (id ∈ left ↔ id ∈ right)) :
    demands.any left.contains = demands.any right.contains := by
  have absent : (demands.any left.contains = false) ↔ (demands.any right.contains = false) := by
    constructor
    · exact fun clear => List.any_eq_false.mpr fun id member found =>
        List.any_eq_false.mp clear id member (List.contains_iff_mem.mpr ((agrees id member).mpr (List.contains_iff_mem.mp found)))
    · exact fun clear => List.any_eq_false.mpr fun id member found =>
        List.any_eq_false.mp clear id member (List.contains_iff_mem.mpr ((agrees id member).mp (List.contains_iff_mem.mp found)))
  cases lhs : demands.any left.contains <;> cases rhs : demands.any right.contains <;> simp_all

theorem register_observations {sig : Signature} {left right : State sig} {tree : OwnedMemory.Tree sig}
    (agrees : left.RegistrationChecksAgree right tree)
    (length : left.accepted.length = right.accepted.length) :
    (left.register tree).map (fun writer => writer.accepted.length) =
      (right.register tree).map (fun writer => writer.accepted.length) := by
  unfold State.register
  dsimp only
  rw [containsAny_eq agrees.owners, containsAny_eq agrees.endpoints]
  split <;> simp [Except.map, length]

theorem indexedClaims_registration {sig : Signature} {left right : State sig}
    (agrees : left.IndexedClaimsAgree right) (tree : OwnedMemory.Tree sig) :
    left.RegistrationChecksAgree right tree := by
  refine ⟨?_, fun id _ => agrees.endpoints id⟩
  intro id _
  simp only [List.map_append, List.mem_append, agrees.accepted, agrees.held]

theorem indexedClaims_spend {sig : Signature} {left right : State sig}
    (agrees : left.IndexedClaimsAgree right) (spend : Spend) :
    (spend.apply left).IndexedClaimsAgree (spend.apply right) := by
  cases spend with
  | owner spent =>
    refine ⟨agrees.accepted, ?_, agrees.endpoints⟩
    intro id
    have membership (state : State sig) :
        id ∈ ((Spend.owner spent).apply state).held.map receiptId ↔ id ∈ state.held.map receiptId ∧ id ≠ spent := by
      simp only [Spend.apply, List.mem_map, List.mem_filter, bne_iff_ne]
      constructor
      · rintro ⟨receipt, ⟨member, fresh⟩, same⟩
        exact ⟨⟨receipt, member, same⟩, same ▸ fresh⟩
      · rintro ⟨⟨receipt, member, same⟩, fresh⟩
        exact ⟨receipt, ⟨member, same.symm ▸ fresh⟩, same⟩
    rw [membership, membership, agrees.held id]
  | endpoint spent =>
    refine ⟨agrees.accepted, agrees.held, ?_⟩
    intro id
    simp only [Spend.apply, List.mem_filter, bne_iff_ne, agrees.endpoints]

theorem indexedClaims_register {sig : Signature} {left right : State sig}
    (agrees : left.IndexedClaimsAgree right) (tree : OwnedMemory.Tree sig) :
    (∃ issue, left.register tree = .error issue ∧ right.register tree = .error issue) ∨
      ∃ lhs rhs, left.register tree = .ok lhs ∧ right.register tree = .ok rhs ∧ lhs.IndexedClaimsAgree rhs := by
  have checks := indexedClaims_registration agrees tree
  simp only [State.register]
  rw [containsAny_eq checks.owners, containsAny_eq checks.endpoints]
  split
  · refine .inr ⟨_, _, rfl, rfl, ⟨congrArg (tree :: ·) agrees.accepted, ?_, ?_⟩⟩
    · intro id
      simp only [List.map_append, List.mem_append, agrees.held]
    · intro id
      simp only [List.mem_append, agrees.endpoints]
  · exact .inl ⟨_, rfl, rfl⟩

theorem accepted_not_endpoint_conflicts {sig : Signature} {tree : OwnedMemory.Tree sig} {id : EndId}
    (unowned : rootReceipts tree = []) (one : rootEndpoints tree = [id]) :
    ∃ first second spent : State sig, ({} : State sig).register tree = .ok first ∧
      spent = (Spend.endpoint id).apply first ∧ first.accepted = spent.accepted ∧
      first.register tree = .error .alias ∧ spent.register tree = .ok second := by
  let first : State sig := ⟨[tree], [], [id]⟩
  let spent := (Spend.endpoint id).apply first
  let second : State sig := ⟨[tree, tree], [], [id]⟩
  exact ⟨first, second, spent, by simp [State.register, unowned, one, first], rfl, rfl,
    by simp [State.register, unowned, one, first], by simp [State.register, unowned, one, first, spent, Spend.apply, second]⟩

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
