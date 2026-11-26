module

public import Silmaril.Formats.Parquet.ListPage.Defs
import all Silmaril.Formats.Parquet.ListPage.Defs
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms

namespace Silmaril.Proofs.Formats.Parquet.ListPage

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListPage

public theorem readEvent_wire {entry : Nat × Nat × Option Int32} {event : Event}
    (h : readEvent entry = .ok event) : event.wire = entry := by
  unfold readEvent at h
  dsimp only at h
  split at h
  · obtain rfl := Except.ok.inj h
    assumption
  · cases h

private theorem readEvents_wire {entries : List (Nat × Nat × Option Int32)} {events : List Event}
    (h : entries.mapM readEvent = .ok events) : events.map Event.wire = entries := by
  induction entries generalizing events with
  | nil => cases h; rfl
  | cons entry rest ih =>
    simp only [List.mapM_cons] at h
    cases first : readEvent entry with
    | error => simp [first, bind, Except.bind] at h
    | ok event =>
      simp only [first, bind, Except.bind] at h
      cases tail : rest.mapM readEvent with
      | error => rw [tail] at h; cases h
      | ok out =>
        rw [tail] at h
        obtain rfl := Except.ok.inj h
        simp [readEvent_wire first, ih tail]

private def liveEvents : Option OpenList → List Event
  | none => []
  | some (head, rest) => .first head :: rest.reverse.map Event.next

private theorem flush_events (active : Option OpenList) (closed : List Row) :
    (flush active closed).reverse.flatMap rowEvents =
      closed.reverse.flatMap rowEvents ++ liveEvents active := by
  cases active with
  | none => simp [flush, liveEvents]
  | some data => cases data; simp [flush, liveEvents, rowEvents]

private theorem go_wire {events : List Event} {active : Option OpenList} {closed rows : List Row}
    (h : reconstruct.go events active closed = .ok rows) :
    rows.flatMap rowEvents = closed.reverse.flatMap rowEvents ++ liveEvents active ++ events := by
  induction events generalizing active closed rows with
  | nil =>
    obtain rfl := Except.ok.inj h
    simpa using flush_events active closed
  | cons event rest ih =>
    cases event with
    | nullList =>
      rw [reconstruct.go] at h
      simpa [liveEvents, List.append_assoc, rowEvents, flush_events] using ih h
    | emptyList =>
      rw [reconstruct.go] at h
      simpa [liveEvents, List.append_assoc, rowEvents, flush_events] using ih h
    | first item =>
      rw [reconstruct.go] at h
      simpa [liveEvents, List.append_assoc, flush_events] using ih h
    | next item =>
      cases active with
      | none =>
        rw [reconstruct.go] at h
        cases h
      | some data =>
        obtain ⟨head, tail⟩ := data
        rw [reconstruct.go] at h
        simpa [liveEvents, List.reverse_cons, List.append_assoc] using ih h

public theorem reconstruct_wire {events : List Event} {rows : List Row}
    (h : reconstruct events = .ok rows) : rows.flatMap rowEvents = events := by
  simpa [liveEvents] using go_wire h

public theorem reconstruct_continuation (item : Option Int32) (rest : List Event) :
    reconstruct (.next item :: rest) = .error .continuationWithoutList := by
  unfold reconstruct
  rw [reconstruct.go]

public theorem decodeBody_wire {limits : Limits} {expectedRows slots : Nat} {body : Bytes}
    {rows : List Row} (h : decodeBody limits expectedRows slots body = .ok rows) :
    Wire limits expectedRows slots body rows := by
  unfold decodeBody at h
  split at h
  · cases h
  rename_i bodyCap
  split at h
  · cases h
  rename_i rowCap
  cases repSplit : FlatPage.splitV1Optional limits.levels.bytes body with
  | error => simp [repSplit, Except.mapError, bind, Except.bind] at h
  | ok first =>
    simp only [repSplit, Except.mapError, bind, Except.bind] at h
    cases defSplit : FlatPage.splitV1Optional limits.levels.bytes first.scalars with
    | error => simp [defSplit] at h
    | ok second =>
      simp only [defSplit] at h
      cases repRead : Hybrid.decode 1 slots limits.levels first.definitions with
      | error => simp [repRead] at h
      | ok reps =>
        simp only [repRead] at h
        cases defRead : Hybrid.decode 2 slots limits.levels second.definitions with
        | error => simp [defRead] at h
        | ok defs =>
          simp only [defRead] at h
          cases plain : Plain.decodeInt32 ((valueMask defs).count true) second.scalars with
          | error => simp [plain] at h
          | ok values =>
            simp only [plain] at h
            cases filled : FlatPage.reconstruct (valueMask defs) values with
            | error => simp [filled] at h
            | ok entries =>
              simp only [filled] at h
              cases eventRead : (reps.zip (defs.zip entries)).mapM readEvent with
              | error => rw [eventRead] at h; cases h
              | ok events =>
                rw [eventRead] at h
                cases assembled : reconstruct events with
                | error => simp [assembled] at h
                | ok output =>
                  simp only [assembled] at h
                  split at h
                  · cases h
                  rename_i count
                  obtain rfl := Except.ok.inj h
                  obtain ⟨repLength, repWidth, repBytes, _, fromBody⟩ :=
                    FlatPage.splitV1Optional_ok_iff.mp repSplit
                  obtain ⟨defLength, defWidth, defBytes, _, fromRest⟩ :=
                    FlatPage.splitV1Optional_ok_iff.mp defSplit
                  obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp filled
                  have defCount := Hybrid.decode_length defRead
                  have entryCount : entries.length = slots := by
                    simpa [valueMask, defCount] using congrArg List.length mask
                  refine ⟨not_not.mp count, ⟨Nat.le_of_not_gt bodyCap, Nat.le_of_not_gt rowCap⟩,
                    repLength, defLength, first.definitions, second.definitions, second.scalars,
                    reps, defs, values, entries, repWidth, defWidth, repBytes, defBytes, ?_,
                    (Hybrid.decode_ok_iff.mp repRead).2.2.2.2, (Hybrid.decode_ok_iff.mp defRead).2.2.2.2,
                    Hybrid.decode_length repRead, defCount, entryCount, plain, mask, ordered, ?_⟩
                  · simpa [fromRest, List.append_assoc] using fromBody
                  · rw [reconstruct_wire assembled]
                    exact readEvents_wire eventRead

public theorem decodeV1_wire {limits : Limits} {codec : Int} {header : Page.Header}
    {expectedRows : Nat} {body : Bytes} {rows : List Row}
    (h : decodeV1 limits codec header expectedRows body = .ok rows) :
    PageWire limits codec header expectedRows body rows := by
  unfold decodeV1 at h
  split at h
  · cases h
  rename_i compression
  split at h
  · rename_i info page
    split at h
    · cases h
    rename_i crc
    split at h
    · cases h
    rename_i encoding
    split at h
    · cases h
    rename_i sizes
    have extent := not_not.mp sizes
    have tags := not_not.mp encoding
    exact ⟨not_not.mp compression, by cases eq : header.crc <;> simp_all, extent.1, extent.2,
      info, page, tags.1, tags.2.1, tags.2.2, decodeBody_wire h⟩
  · cases h

end Silmaril.Proofs.Formats.Parquet.ListPage
