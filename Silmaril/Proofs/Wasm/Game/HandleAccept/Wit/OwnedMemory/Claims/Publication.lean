module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Publication.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication

open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled Silmaril.Wasm.Component.Runtime

private theorem register_preserves {sig : Signature} {before after : State sig} {tree : OwnedMemory.Tree sig}
    (registered : before.register tree = .ok after) (unique : before.publishedOwners.Nodup) :
    after.publishedOwners.Nodup := by
  unfold State.register at registered
  dsimp only at registered
  split at registered
  next allowed =>
    cases registered
    simp only [State.publishedOwners, List.flatMap_cons, List.map_append]
    refine List.nodup_append.mpr ⟨allowed.1, unique, ?_⟩
    intro newOwner fresh oldOwner known same
    subst oldOwner
    have allKnown : newOwner ∈ ((before.accepted.flatMap rootReceipts ++ before.held).map receiptId) := by
      rw [List.map_append]
      exact List.mem_append_left _ known
    have noneKnown : ((rootReceipts tree).map receiptId).any
        (((before.accepted.flatMap rootReceipts ++ before.held).map receiptId).contains) = false := by
      simpa using allowed.2.1
    have absent := List.any_eq_false.mp noneKnown newOwner fresh
    rw [List.contains_iff_mem.mpr allKnown] at absent
    contradiction
  next => contradiction

theorem run_preserves {sig : Signature} {before after : State sig} (run : WriterRun before after)
    (unique : before.publishedOwners.Nodup) : after.publishedOwners.Nodup := by
  induction run with
  | refl => exact unique
  | cons step _ ih =>
    apply ih
    cases step with
    | same => exact unique
    | publish _ registered => exact register_preserves registered unique
    | spend update => cases update <;> exact unique

theorem run_backed {sig : Signature} {before after : State sig} (run : WriterRun before after)
    (backed : before.ClaimsBacked) : after.ClaimsBacked := by
  induction run with
  | refl => exact backed
  | cons step _ ih =>
    apply ih
    cases step with
    | same => exact backed
    | publish tree registered =>
      have claims := register_claims registered
      unfold State.ClaimsBacked
      rw [claims.1, claims.2.1, List.flatMap_cons]
      exact (List.Sublist.refl (rootReceipts tree)).append backed
    | spend update =>
      cases update with
      | owner => exact List.filter_sublist.trans backed
      | endpoint => exact backed

theorem prepared_from_history {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (backed : state.ClaimsBacked) (success : state.prepare resource id = .ok (representation, spent)) :
    ∃ tree ∈ state.accepted, ∃ receipt ∈ rootReceipts tree,
      receiptId receipt = id ∧ receipt.1 = resource ∧ receipt.2.representation = representation := by
  obtain ⟨receipt, live, origin⟩ := prepare_provenance success
  obtain ⟨tree, accepted, captured⟩ := List.mem_flatMap.mp (backed.subset live)
  exact ⟨tree, accepted, receipt, captured, origin⟩

theorem prepared_retires {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (backed : state.ClaimsBacked) (success : state.prepare resource id = .ok (representation, spent)) :
    spent.retiredOwner id := by
  obtain ⟨receipt, live, same, _, _⟩ := prepare_provenance success
  obtain ⟨history, remaining⟩ := prepare_spends success
  refine ⟨?_, ?_⟩
  · rw [history]
    exact List.mem_map.mpr ⟨receipt, backed.subset live, same⟩
  · intro member
    obtain ⟨entry, held, equal⟩ := List.mem_map.mp member
    exact ((remaining entry).mp held).2 equal

theorem retired_refuses {sig : Signature} {state : State sig} {id : HandleObjId}
    (retired : state.retiredOwner id) (resource : RtId) :
    state.prepare resource id = .error .unclaimed := by
  have absent : state.held.find? (fun entry => receiptId entry == id) = none :=
    List.find?_eq_none.mpr fun receipt member equal =>
      retired.2 (List.mem_map.mpr ⟨receipt, member, beq_iff_eq.mp equal⟩)
  simp [State.prepare, absent]

theorem held_publication {sig : Signature} {before after : HostState sig} {receipt : Receipt}
    (journal : PublicationDelta before after) (run : WriterRun before.writer after.writer)
    (backed : after.writer.ClaimsBacked) (held : receipt ∈ after.writer.held)
    (fresh : receiptId receipt ∉ before.writer.publishedOwners) :
    ∃ position ticket handle, before.publications.length ≤ position ∧
      after.RecordsOwner position ticket handle receipt := by
  obtain ⟨entries, roots, publications, history, lengths, targets⟩ := journal.targets run
  obtain ⟨root, inHistory, introduced⟩ := List.mem_flatMap.mp (backed.subset held)
  have newRoot : root ∈ roots := by
    rw [history, List.mem_append] at inHistory
    rcases inHistory with newRoot | priorRoot
    · exact newRoot
    · exact (fresh (List.mem_map.mpr ⟨receipt,
        List.mem_flatMap.mpr ⟨root, priorRoot, introduced⟩, rfl⟩)).elim
  obtain ⟨offset, lookup⟩ := List.mem_iff_getElem?.mp newRoot
  have offsetBound := (List.getElem?_eq_some_iff.mp lookup).1
  let index := roots.length - (offset + 1)
  have indexBound : index < entries.length := by unfold index; omega
  cases value : entries[index]'indexBound with
  | mk ticket handle =>
    have entry : entries[index]? = some (ticket, handle) := by
      rw [List.getElem?_eq_getElem indexBound, value]
    obtain ⟨target, rootLookup, selected⟩ := targets index ticket handle entry
    have sameOffset : roots.length - (index + 1) = offset := by unfold index; omega
    rw [sameOffset, lookup] at rootLookup
    cases Option.some.inj rootLookup
    have handleBound : handle < 2 ^ 32 := by
      obtain ⟨entries', same, _, inRange⟩ := journal
      have sameEntries : entries' = entries := List.append_cancel_left (same.symm.trans publications)
      subst entries'
      exact (inRange index ticket handle entry).2
    refine ⟨before.publications.length + index, ticket, handle, by omega, ?_, handleBound, root, selected,
      introduced⟩
    rw [publications, List.getElem?_append_right (by omega)]
    simpa using entry

theorem prepared_publication {sig : Signature} {before after : HostState sig} {spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (journal : PublicationDelta before after) (run : WriterRun before.writer after.writer)
    (backed : before.writer.ClaimsBacked) (fresh : id ∉ before.writer.publishedOwners)
    (success : after.writer.prepare resource id = .ok (representation, spent)) :
    ∃ position ticket handle receipt, before.publications.length ≤ position ∧
      after.RecordsOwner position ticket handle receipt ∧
      receiptId receipt = id ∧ receipt.1 = resource ∧ receipt.2.representation = representation := by
  obtain ⟨receipt, held, identity, nominal, rep⟩ := prepare_provenance success
  obtain ⟨position, ticket, handle, suffix, recorded⟩ := held_publication journal run (run_backed run backed)
    held (identity.symm ▸ fresh)
  exact ⟨position, ticket, handle, receipt, suffix, recorded, identity, nominal, rep⟩

theorem retained_owner_record {sig : Signature} {before after : HostState sig}
    {position ticket handle : Nat} {receipt : Receipt} (journal : PublicationDelta before after)
    (run : WriterRun before.writer after.writer) (recorded : before.RecordsOwner position ticket handle receipt) :
    after.RecordsOwner position ticket handle receipt := by
  obtain ⟨entry, bound, root, selected, captured⟩ := recorded
  obtain ⟨_, appended, _, _⟩ := journal
  refine ⟨?_, bound, root, run.retains_target selected, captured⟩
  rwa [appended, List.getElem?_append_left (List.getElem?_eq_some_iff.mp entry).1]

theorem publication_roots {sig : Signature} {before after : HostState sig}
    (journal : PublicationDelta before after) (run : WriterRun before.writer after.writer) :
    after.publicationRootsFrom before.publications.length =
      (after.writer.accepted.reverse.drop before.writer.accepted.length).map some := by
  obtain ⟨entries, roots, appended, accepted, count, targets⟩ := journal.targets run
  obtain ⟨boundedEntries, boundedAppended, _, bounded⟩ := journal
  have sameEntries : boundedEntries = entries := List.append_cancel_left (boundedAppended.symm.trans appended)
  subst boundedEntries
  unfold HostState.publicationRootsFrom
  rw [appended, List.drop_left]
  rw [show after.writer.accepted.reverse.drop before.writer.accepted.length = roots.reverse by
    rw [accepted, List.reverse_append]
    exact List.drop_left' (by simp)]
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map]
  cases entry : entries[index]? with
  | none =>
    have past : entries.length ≤ index := List.getElem?_eq_none_iff.mp entry
    rw [List.getElem?_eq_none (by simpa only [List.length_reverse, ← count] using past)]
    rfl
  | some pair =>
    rcases pair with ⟨ticket, handle⟩
    obtain ⟨tree, lookup, selected⟩ := targets index ticket handle entry
    have inRange : index < roots.length := count ▸ (List.getElem?_eq_some_iff.mp entry).1
    rw [List.getElem?_reverse inRange]
    simp only [Option.map_some, Nat.sub_sub, Nat.add_comm 1, lookup,
      ite_eq_left (bounded index ticket handle entry).2, selected]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication
