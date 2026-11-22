module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Object)

private theorem prepareOwner_live {sig : Signature} {left right : State sig}
    (agrees : left.LiveClaimsAgree right) (receipt : Receipt) :
    (∃ issue, prepareOwner left receipt = .error issue ∧ prepareOwner right receipt = .error issue) ∨
      ∃ rep lhs rhs, prepareOwner left receipt = .ok (rep, lhs) ∧ prepareOwner right receipt = .ok (rep, rhs) ∧
        lhs.LiveClaimsAgree rhs := by
  have observed := agrees.prepare receipt.1 (receiptId receipt)
  cases first : left.prepare receipt.1 (receiptId receipt) with
  | error issue =>
    cases second : right.prepare receipt.1 (receiptId receipt) with
    | error peer =>
      simp [first, second, Except.map] at observed
      subst peer
      exact .inl ⟨.claims issue, by simp [prepareOwner, first, Except.mapError, bind, Except.bind],
        by simp [prepareOwner, second, Except.mapError, bind, Except.bind]⟩
    | ok _ => simp [first, second, Except.map] at observed
  | ok result =>
    obtain ⟨rep, lhs⟩ := result
    obtain ⟨rhs, second, next⟩ := agrees.prepare_success first
    by_cases equal : rep = receipt.2.representation
    · exact .inr ⟨rep, lhs, rhs, by simp [prepareOwner, first, Except.mapError, bind, Except.bind, equal]; rfl,
        by simp [prepareOwner, second, Except.mapError, bind, Except.bind, equal]; rfl, next⟩
    · exact .inl ⟨.ownerReceipt, by simp [prepareOwner, first, Except.mapError, bind, Except.bind, equal]; rfl,
        by simp [prepareOwner, second, Except.mapError, bind, Except.bind, equal]; rfl⟩

theorem prepare_live {E : CoreEngine} {sig : Signature} (store : CStore E)
    (plan : List Object) {left right : State sig} (agrees : left.LiveClaimsAgree right) :
    prepare store left plan = prepare store right plan := by
  induction plan generalizing left right with
  | nil => rfl
  | cons object rest ih =>
    cases object with
    | owner receipt =>
      rcases prepareOwner_live agrees receipt with ⟨issue, first, second⟩ | ⟨rep, lhs, rhs, first, second, next⟩
      · simp [prepare, first, second, bind, Except.bind]
      · simpa [prepare, first, second, bind, Except.bind] using ih next
    | shared object =>
      cases object with
      | endpoint channel element id =>
        by_cases present : id ∈ right.endpoints
        · have leftPresent := (agrees.endpoints id).mpr present
          cases ready : Async.Transfer.readyToGive store channel element ⟨id⟩ with
          | error _ =>
            simp [prepare, prepareEndpoint, State.spendEndpoint, Except.mapError, leftPresent, present, ready,
              bind, Except.bind]
          | ok _ =>
            simp [prepare, prepareEndpoint, State.spendEndpoint, Except.mapError, leftPresent, present, ready,
              bind, Except.bind]
            exact ih (agrees.spend (.endpoint id))
        · have leftAbsent := mt (agrees.endpoints id).mp present
          simp [prepare, prepareEndpoint, State.spendEndpoint, Except.mapError, leftAbsent, present, bind, Except.bind]
      | errorContext id =>
        simp only [prepare]
        split
        · exact ih agrees
        · rfl

private theorem after_spend {sig : Signature} {state : State sig} {spent later : Spend}
    (held : later.Live (spent.apply state)) : later ≠ spent ∧ later.Live state := by
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
    (held : spend.Live state) (distinct : spends.Nodup)
    (tail : ∀ later ∈ spends, later.Live (spend.apply state)) :
    (spend :: spends).Nodup ∧ ∀ later ∈ spend :: spends, later.Live state := by
  refine ⟨List.nodup_cons.mpr ⟨fun member => (after_spend (tail spend member)).1 rfl, distinct⟩, ?_⟩
  intro later member
  rcases List.mem_cons.mp member with rfl | member
  · exact held
  · exact (after_spend (tail later member)).2

theorem owner_prepared {sig : Signature} {state next : State sig} {receipt : Receipt} {rep : Nat}
    (checked : prepareOwner state receipt = .ok (rep, next)) :
    next = (Spend.owner (receiptId receipt)).apply state ∧ (Spend.owner (receiptId receipt)).Live state := by
  cases found : state.held.find? (fun entry => receiptId entry == receiptId receipt) with
  | none =>
    simp [prepareOwner, State.prepare, Except.mapError, found] at checked
    cases checked
  | some selected =>
    have equal := List.find?_some found
    have identity : receiptId selected = receiptId receipt := beq_iff_eq.mp equal
    have present : (Spend.owner (receiptId receipt)).Live state :=
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

theorem endpoint_prepared {E : CoreEngine} {sig : Signature} {store : CStore E}
    {state next : State sig} {channel element id}
    (checked : prepareEndpoint store state channel element id = .ok next) :
    next = (Spend.endpoint id).apply state ∧ (Spend.endpoint id).Live state := by
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
    (exclusiveSpends plan).Nodup ∧ ∀ spend ∈ exclusiveSpends plan, spend.Live state := by
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
