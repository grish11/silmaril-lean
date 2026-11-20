module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Object)

private def Held {sig : Signature} (state : State sig) : Spend → Prop
  | .owner id => id ∈ state.held.map receiptId
  | .endpoint id => id ∈ state.endpoints

private theorem after_spend {sig : Signature} {state : State sig} {spent later : Spend}
    (held : Held (spent.apply state) later) : later ≠ spent ∧ Held state later := by
  cases spent <;> cases later
  case owner.owner spent later =>
    obtain ⟨receipt, kept, identity⟩ := List.mem_map.mp held
    obtain ⟨member, different⟩ := List.mem_filter.mp kept
    refine ⟨?_, List.mem_map.mpr ⟨receipt, member, identity⟩⟩
    intro equal
    cases equal
    simp [identity] at different
  case endpoint.endpoint spent later =>
    obtain ⟨member, different⟩ := List.mem_filter.mp held
    refine ⟨?_, member⟩
    intro equal
    cases equal
    simp at different
  all_goals exact ⟨(by intro equal; cases equal), held⟩

private theorem prepend {sig : Signature} {state : State sig} {spend : Spend} {spends : List Spend}
    (held : Held state spend) (distinct : spends.Nodup)
    (tail : ∀ later ∈ spends, Held (spend.apply state) later) :
    (spend :: spends).Nodup ∧ ∀ later ∈ spend :: spends, Held state later := by
  refine ⟨List.nodup_cons.mpr ⟨fun member => (after_spend (tail spend member)).1 rfl, distinct⟩, ?_⟩
  intro later member
  rcases List.mem_cons.mp member with rfl | member
  · exact held
  · exact (after_spend (tail later member)).2

private theorem owner_prepared {sig : Signature} {state next : State sig} {receipt : Receipt} {rep : Nat}
    (checked : prepareOwner state receipt = .ok (rep, next)) :
    next = (Spend.owner (receiptId receipt)).apply state ∧ Held state (.owner (receiptId receipt)) := by
  cases found : state.held.find? (fun entry => receiptId entry == receiptId receipt) with
  | none =>
    simp [prepareOwner, State.prepare, Except.mapError, found] at checked
    cases checked
  | some selected =>
    have equal := List.find?_some found
    have identity : receiptId selected = receiptId receipt := beq_iff_eq.mp equal
    have present : Held state (.owner (receiptId receipt)) :=
      List.mem_map.mpr ⟨selected, List.mem_of_find?_eq_some found, identity⟩
    by_cases typed : selected.1 = receipt.1
    · simp [prepareOwner, State.prepare, Except.mapError, found, typed] at checked
      change (if selected.2.representation = receipt.2.representation then
        Except.ok (selected.2.representation, (Spend.owner (receiptId receipt)).apply state)
        else Except.error _) = .ok (rep, next) at checked
      split at checked
      · exact ⟨(congrArg Prod.snd (Except.ok.inj checked)).symm, present⟩
      · cases checked
    · simp [prepareOwner, State.prepare, Except.mapError, found, typed] at checked
      cases checked

private theorem endpoint_prepared {E : CoreEngine} {sig : Signature} {store : CStore E}
    {state next : State sig} {channel element id}
    (checked : prepareEndpoint store state channel element id = .ok next) :
    next = (Spend.endpoint id).apply state ∧ Held state (.endpoint id) := by
  by_cases present : id ∈ state.endpoints
  · refine ⟨?_, present⟩
    cases ready : Async.Transfer.readyToGive store channel element ⟨id⟩ with
    | error _ =>
      simp [prepareEndpoint, State.spendEndpoint, Except.mapError, present, ready] at checked
      cases checked
    | ok _ =>
      simp [prepareEndpoint, State.spendEndpoint, Except.mapError, present, ready] at checked
      exact (Except.ok.inj checked).symm
  · simp [prepareEndpoint, State.spendEndpoint, Except.mapError, present] at checked
    cases checked

private theorem prepared {E : CoreEngine} {sig : Signature} (store : CStore E)
    (state : State sig) (plan : List Object) (checked : prepare store state plan = .ok ()) :
    (exclusiveSpends plan).Nodup ∧ ∀ spend ∈ exclusiveSpends plan, Held state spend := by
  induction plan generalizing state with
  | nil => simp [exclusiveSpends]
  | cons object rest ih =>
    cases object with
    | owner receipt =>
      cases head : prepareOwner state receipt with
      | error issue =>
        rw [prepare, head] at checked
        cases checked
      | ok value =>
        obtain ⟨rep, next⟩ := value
        obtain ⟨rfl, held⟩ := owner_prepared head
        rw [prepare, head] at checked
        have tail := ih _ checked
        exact prepend held tail.1 tail.2
    | shared object =>
      cases object with
      | endpoint channel element id =>
        cases head : prepareEndpoint store state channel element id with
        | error issue =>
          rw [prepare, head] at checked
          cases checked
        | ok next =>
          obtain ⟨rfl, held⟩ := endpoint_prepared head
          rw [prepare, head] at checked
          have tail := ih _ checked
          exact prepend held tail.1 tail.2
      | errorContext id =>
        cases present : (store.errCtx? id).isSome
        · simp [prepare, present] at checked
        · exact ih _ (by simpa [prepare, present] using checked)

theorem prepare_distinct {E : CoreEngine} {sig : Signature} (store : CStore E)
    (state : State sig) (plan : List Object) (checked : prepare store state plan = .ok ()) :
    (exclusiveSpends plan).Nodup := (prepared store state plan checked).1

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare
