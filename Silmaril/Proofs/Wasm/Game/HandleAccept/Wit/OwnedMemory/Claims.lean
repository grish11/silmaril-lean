module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims

open Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory (Receipt)

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

private theorem owner_spend_membership {sig : Signature} (state : State sig) (spent id : HandleObjId) :
    id ∈ ((Spend.owner spent).apply state).held.map receiptId ↔ id ∈ state.held.map receiptId ∧ id ≠ spent := by
  simp only [Spend.apply, List.mem_map, List.mem_filter, bne_iff_ne]
  constructor
  · rintro ⟨receipt, ⟨member, fresh⟩, same⟩
    exact ⟨⟨receipt, member, same⟩, same ▸ fresh⟩
  · rintro ⟨⟨receipt, member, same⟩, fresh⟩
    exact ⟨receipt, ⟨member, same.symm ▸ fresh⟩, same⟩

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
    rw [owner_spend_membership, owner_spend_membership, agrees.held id]
  | endpoint spent =>
    refine ⟨agrees.accepted, agrees.held, ?_⟩
    intro id
    simp only [Spend.apply, List.mem_filter, bne_iff_ne, agrees.endpoints]

theorem registration_after_left_spend {sig : Signature} {left right : State sig} {tree : OwnedMemory.Tree sig}
    (agrees : left.RegistrationChecksAgree right tree) (update : Spend)
    (frames : update.FramesRegistration left tree) :
    (update.apply left).RegistrationChecksAgree right tree := by
  cases update with
  | owner spent =>
    refine ⟨?_, agrees.endpoints⟩
    intro id demand
    rw [← agrees.owners id demand]
    simp only [List.map_append, List.mem_append]
    rw [owner_spend_membership]
    have unchanged : ((Spend.owner spent).apply left).accepted = left.accepted := rfl
    rw [unchanged]
    by_cases same : id = spent
    · subst id
      unfold Spend.FramesRegistration at frames
      cases frames with
      | inl absent => exact (absent demand).elim
      | inr historical => simp only [historical, true_or]
    · exact ⟨fun member => member.elim Or.inl (fun kept => Or.inr kept.1),
        fun member => member.elim Or.inl (fun kept => Or.inr ⟨kept, same⟩)⟩
  | endpoint spent =>
    refine ⟨agrees.owners, ?_⟩
    intro id demand
    have different : id ≠ spent := fun same => frames (same ▸ demand)
    simpa [Spend.apply, List.mem_filter, different] using agrees.endpoints id demand

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

private theorem ownerObservation_none {sig : Signature} (state : State sig) (id : HandleObjId) :
    state.ownerObservation id = none ↔ id ∉ state.held.map receiptId := by
  have erase : state.ownerObservation id = none ↔ state.held.find? (fun receipt => receiptId receipt == id) = none := by
    unfold State.ownerObservation
    cases (state.held.find? (fun receipt => receiptId receipt == id)) <;> simp
  rw [erase, List.find?_eq_none]
  constructor
  · intro absent member
    obtain ⟨receipt, present, rfl⟩ := List.mem_map.mp member
    simpa using absent receipt present
  · intro absent receipt member
    have distinct : receiptId receipt ≠ id := fun same => absent (List.mem_map.mpr ⟨receipt, member, same⟩)
    simp [distinct]

theorem liveClaims_indexed {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) : left.IndexedClaimsAgree right := by
  refine ⟨agrees.accepted, ?_, agrees.endpoints⟩
  intro id
  rw [← not_iff_not, ← ownerObservation_none, ← ownerObservation_none, agrees.owners]

private theorem findOwner_filter (held : List Receipt) (spent id : HandleObjId) :
    (held.filter (fun receipt => receiptId receipt != spent)).find? (fun receipt => receiptId receipt == id) =
      if id = spent then none else held.find? (fun receipt => receiptId receipt == id) := by
  rw [List.find?_filter]
  by_cases same : id = spent
  · subst spent
    simp
  · rw [ite_eq_right same]
    congr 1
    funext receipt
    by_cases found : receiptId receipt = id <;> simp_all

theorem liveClaims_spend {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) (update : Spend) :
    (update.apply left).LiveClaimsAgree (update.apply right) := by
  cases update with
  | owner spent =>
    refine ⟨agrees.accepted, ?_, agrees.endpoints⟩
    intro id
    simp only [State.ownerObservation, Spend.apply, findOwner_filter]
    by_cases same : id = spent
    · simp only [ite_eq_left same]
    · simp only [ite_eq_right same]
      exact agrees.owners id
  | endpoint spent =>
    refine ⟨agrees.accepted, agrees.owners, ?_⟩
    intro id
    simp only [Spend.apply, List.mem_filter, bne_iff_ne, agrees.endpoints]

theorem spend_not_live {sig : Signature} (update : Spend) (state : State sig) : ¬ update.Live (update.apply state) := by
  cases update with
  | owner id =>
    intro live
    obtain ⟨receipt, kept, same⟩ := List.mem_map.mp live
    have different := (List.mem_filter.mp kept).2
    simp [same] at different
  | endpoint id => simp [Spend.Live, Spend.apply]

theorem liveClaims_asymmetricSpend {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) {update : Spend} (live : update.Live left) :
    (update.apply left).LiveClaimsAgree (update.apply right) ∧ ¬ (update.apply left).LiveClaimsAgree right := by
  refine ⟨liveClaims_spend agrees update, fun wronglyRestored => spend_not_live update left ?_⟩
  have before := liveClaims_indexed agrees
  have after := liveClaims_indexed wronglyRestored
  cases update with
  | owner id => exact (after.held id).mpr ((before.held id).mp live)
  | endpoint id => exact (after.endpoints id).mpr ((before.endpoints id).mp live)

private theorem prepare_observation {sig : Signature} (state : State sig) (resource : RtId) (id : HandleObjId) :
    (state.prepare resource id).map Prod.fst = match state.ownerObservation id with
    | none => .error .unclaimed
    | some (nominal, representation) =>
      if nominal != resource then .error .wrongResourceType else .ok representation := by
  unfold State.prepare State.ownerObservation
  cases state.held.find? (fun receipt => receiptId receipt == id) with
  | none => rfl
  | some receipt => by_cases typed : receipt.1 = resource <;> simp [Except.map, typed]

theorem liveClaims_prepare {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) (resource : RtId) (id : HandleObjId) :
    (left.prepare resource id).map Prod.fst = (right.prepare resource id).map Prod.fst := by
  rw [prepare_observation, prepare_observation, agrees.owners]

theorem prepare_after_left_spend {sig : Signature} {left right : State sig} (update : Spend)
    (resource : RtId) (id : HandleObjId) (agrees : left.ownerObservation id = right.ownerObservation id)
    (frames : ∀ spent, update = .owner spent → id ≠ spent) :
    ((update.apply left).prepare resource id).map Prod.fst = (right.prepare resource id).map Prod.fst := by
  rw [prepare_observation, prepare_observation]
  congr 1
  rw [← agrees]
  cases update with
  | endpoint => rfl
  | owner spent => simp only [State.ownerObservation, Spend.apply, findOwner_filter, ite_eq_right (frames spent rfl)]

theorem liveClaims_prepare_success {sig : Signature} {left right next : State sig}
    (agrees : left.LiveClaimsAgree right) {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : left.prepare resource id = .ok (representation, next)) :
    ∃ peer, right.prepare resource id = .ok (representation, peer) ∧ next.LiveClaimsAgree peer := by
  have paired := liveClaims_prepare agrees resource id
  rw [success] at paired
  cases compared : right.prepare resource id with
  | error issue => simp [compared, Except.map] at paired
  | ok result =>
    obtain ⟨rep, peer⟩ := result
    simp [compared, Except.map] at paired
    subst rep
    have update (state updated : State sig) (step : state.prepare resource id = .ok (representation, updated)) :
        updated = (Spend.owner id).apply state := by
      unfold State.prepare at step
      split at step <;> try contradiction
      split at step <;> cases step
      rfl
    exact ⟨peer, rfl, by rw [update _ _ success, update _ _ compared]; exact liveClaims_spend agrees _⟩

theorem liveClaims_register {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) (tree : OwnedMemory.Tree sig) :
    (∃ issue, left.register tree = .error issue ∧ right.register tree = .error issue) ∨
      ∃ lhs rhs, left.register tree = .ok lhs ∧ right.register tree = .ok rhs ∧ lhs.LiveClaimsAgree rhs := by
  rcases indexedClaims_register (liveClaims_indexed agrees) tree with failure | ⟨lhs, rhs, first, second, matched⟩
  · exact .inl failure
  refine .inr ⟨lhs, rhs, first, second, ⟨matched.accepted, ?_, matched.endpoints⟩⟩
  intro id
  simp only [State.ownerObservation, (register_claims first).2.1, (register_claims second).2.1, List.find?_append]
  cases (rootReceipts tree).find? (fun receipt => receiptId receipt == id)
  · exact agrees.owners id
  · rfl

theorem indexed_not_owner_observations {sig : Signature} (resource : RtId) (identity : HandleObjId)
    {rep other : Nat} (different : rep ≠ other) :
    ∃ left right : State sig, left.IndexedClaimsAgree right ∧
      (left.prepare resource identity).map Prod.fst ≠ (right.prepare resource identity).map Prod.fst := by
  refine ⟨{ held := [⟨resource, ⟨identity, rep⟩⟩] }, { held := [⟨resource, ⟨identity, other⟩⟩] },
    ⟨rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩, ?_⟩
  simpa [State.prepare, receiptId, Except.map] using different

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
