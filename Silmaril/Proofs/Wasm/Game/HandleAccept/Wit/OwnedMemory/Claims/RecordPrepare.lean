module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Observation.Defs
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

theorem prepareOwner_observed {sig : Signature} {left right : State sig} (receipt : Receipt)
    (agrees : (Spend.owner (receiptId receipt)).ObservationAgrees left right) :
    (prepareOwner left receipt).map Prod.fst = (prepareOwner right receipt).map Prod.fst := by
  have observed := State.prepare_observation_eq receipt.1 (receiptId receipt) agrees
  cases first : left.prepare receipt.1 (receiptId receipt) with
  | error issue =>
    cases second : right.prepare receipt.1 (receiptId receipt) with
    | error peer =>
      simp [first, second, Except.map] at observed
      subst peer
      simp [prepareOwner, first, second, Except.mapError, Except.map, bind, Except.bind]
    | ok _ => simp [first, second, Except.map] at observed
  | ok result =>
    cases second : right.prepare receipt.1 (receiptId receipt) with
    | error _ => simp [first, second, Except.map] at observed
    | ok peer =>
      obtain ⟨rep, lhs⟩ := result
      obtain ⟨other, rhs⟩ := peer
      simp [first, second, Except.map] at observed
      subst other
      by_cases equal : rep = receipt.2.representation <;>
        simp [prepareOwner, first, second, Except.mapError, Except.map, bind, Except.bind, equal] <;> rfl

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

theorem prepare_observations {E : CoreEngine} {sig : Signature} (store : CStore E)
    (plan : List Object) {left right : State sig}
    (agrees : ∀ probe ∈ exclusiveSpends plan, probe.ObservationAgrees left right) :
    prepare store left plan = prepare store right plan := by
  induction plan generalizing left right with
  | nil => rfl
  | cons object rest ih =>
    cases object with
    | owner receipt =>
      have head := prepareOwner_observed receipt (agrees (.owner (receiptId receipt)) (by simp [exclusiveSpends]))
      cases first : prepareOwner left receipt with
      | error issue =>
        cases second : prepareOwner right receipt with
        | error peer =>
          simp [first, second, Except.map] at head
          subst peer
          simp [prepare, first, second, bind, Except.bind]
        | ok _ => simp [first, second, Except.map] at head
      | ok result =>
        cases second : prepareOwner right receipt with
        | error _ => simp [first, second, Except.map] at head
        | ok peer =>
          obtain ⟨rep, lhs⟩ := result
          obtain ⟨other, rhs⟩ := peer
          obtain ⟨rfl, _⟩ := owner_prepared first
          obtain ⟨rfl, _⟩ := owner_prepared second
          simpa [prepare, first, second, bind, Except.bind] using ih
            (fun probe member => (agrees probe (List.mem_cons_of_mem _ member)).spend (.owner (receiptId receipt)))
    | shared object =>
      cases object with
      | endpoint channel element id =>
        have same : id ∈ left.endpoints ↔ id ∈ right.endpoints := agrees (.endpoint id) (by simp [exclusiveSpends])
        by_cases present : id ∈ right.endpoints
        · have leftPresent := same.mpr present
          cases ready : Async.Transfer.readyToGive store channel element ⟨id⟩ with
          | error _ =>
            simp [prepare, prepareEndpoint, State.spendEndpoint, Except.mapError, leftPresent, present, ready,
              bind, Except.bind]
          | ok _ =>
            simp [prepare, prepareEndpoint, State.spendEndpoint, Except.mapError, leftPresent, present, ready,
              bind, Except.bind]
            exact ih (fun probe member => (agrees probe (List.mem_cons_of_mem _ member)).spend (.endpoint id))
        · have leftAbsent := mt same.mp present
          simp [prepare, prepareEndpoint, State.spendEndpoint, Except.mapError, leftAbsent, present, bind, Except.bind]
      | errorContext id =>
        simp only [prepare]
        split
        · exact ih agrees
        · rfl

theorem prepare_live {E : CoreEngine} {sig : Signature} (store : CStore E)
    (plan : List Object) {left right : State sig} (agrees : left.LiveClaimsAgree right) :
    prepare store left plan = prepare store right plan :=
  prepare_observations store plan (fun probe _ => agrees.observe probe)

theorem prepare_conflict {E : CoreEngine} {sig : Signature} (store : CStore E)
    (plan : List Object) {left right : State sig} {pending : Spend → Prop}
    (related : left.ClaimDiscrepancies right pending)
    (unequal : prepare store left plan ≠ prepare store right plan) :
    ∃ probe, pending probe ∧ ReachedPrepareConflict store left right plan probe := by
  induction plan generalizing left right pending with
  | nil => exact False.elim (unequal rfl)
  | cons object rest ih =>
    classical
    cases object with
    | owner receipt =>
      by_cases agrees : (Spend.owner (receiptId receipt)).ObservationAgrees left right
      · have head := prepareOwner_observed receipt agrees
        cases checked : prepareOwner left receipt with
        | error issue =>
          cases raw : prepareOwner right receipt with
          | error other =>
            have equal : issue = other := by simpa [checked, raw, Except.map] using head
            exact False.elim (unequal (by simp [prepare, checked, raw, equal, bind, Except.bind]))
          | ok _ => simp [checked, raw, Except.map] at head
        | ok lhs =>
          cases raw : prepareOwner right receipt with
          | error _ => simp [checked, raw, Except.map] at head
          | ok rhs =>
            obtain ⟨rep, lhs⟩ := lhs
            obtain ⟨other, rhs⟩ := rhs
            have equal : rep = other := by simpa [checked, raw, Except.map] using head
            subst other
            obtain ⟨rfl, _⟩ := owner_prepared checked
            obtain ⟨rfl, _⟩ := owner_prepared raw
            obtain ⟨probe, bounded, conflict⟩ := ih (related.spendBoth (.owner (receiptId receipt)))
              (by simpa [prepare, checked, raw, bind, Except.bind] using unequal)
            exact ⟨probe, bounded.1, .afterOwner agrees checked raw conflict⟩
      · exact ⟨.owner (receiptId receipt), not_not.mp (fun absent => agrees (related.observe _ absent)), .owner agrees⟩
    | shared object =>
      cases object with
      | endpoint channel element id =>
        by_cases agrees : (Spend.endpoint id).ObservationAgrees left right
        · by_cases present : id ∈ right.endpoints
          · have leftPresent := agrees.mpr present
            cases ready : Async.Transfer.readyToGive store channel element ⟨id⟩ with
            | error issue =>
              exact False.elim (unequal (by simp [prepare, prepareEndpoint, State.spendEndpoint,
                Except.mapError, leftPresent, present, ready, bind, Except.bind]))
            | ok value =>
              have checked : prepareEndpoint store left channel element id = .ok ((Spend.endpoint id).apply left) := by
                simp [prepareEndpoint, State.spendEndpoint, Except.mapError, leftPresent, ready, bind, Except.bind, pure, Except.pure]
              have raw : prepareEndpoint store right channel element id = .ok ((Spend.endpoint id).apply right) := by
                simp [prepareEndpoint, State.spendEndpoint, Except.mapError, present, ready, bind, Except.bind, pure, Except.pure]
              obtain ⟨probe, bounded, conflict⟩ := ih (related.spendBoth (.endpoint id))
                (by simpa [prepare, checked, raw, bind, Except.bind] using unequal)
              exact ⟨probe, bounded.1, .afterEndpoint agrees checked raw conflict⟩
          · have leftAbsent := mt agrees.mp present
            exact False.elim (unequal (by simp [prepare, prepareEndpoint, State.spendEndpoint,
              Except.mapError, leftAbsent, present, bind, Except.bind]))
        · exact ⟨.endpoint id, not_not.mp (fun absent => agrees (related.observe _ absent)), .endpoint agrees⟩
      | errorContext id =>
        cases found : (store.errCtx? id).isSome
        · exact False.elim (unequal (by simp [prepare, found]))
        · obtain ⟨probe, bounded, conflict⟩ := ih related (by simpa [prepare, found] using unequal)
          exact ⟨probe, bounded, .afterContext found conflict⟩

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
