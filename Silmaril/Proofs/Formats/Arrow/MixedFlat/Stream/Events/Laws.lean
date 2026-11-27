module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs
public import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Events

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.Events MixedFlat.Stream.Events

private def StepSpec (limits : MixedFlat.Limits) (input : KBytes)
    (fields : List MixedFlat.Field) (remaining ordinal rows offset : Nat)
    (reply : Except MixedFlat.Stream.Events.Error (Option (Decoded fields))) : Prop :=
    match reply with
    | .error error => ∃ cause, error = .message ordinal offset cause ∧
        MixedFlat.Stream.readBatches limits input fields remaining ordinal rows offset =
          .error (.batch ordinal cause)
    | .ok none =>
        readEnvelope limits.observation.ipc input offset = .ok .eos ∧ offset + 8 = input.len ∧
        MixedFlat.Stream.readBatches limits input fields remaining ordinal rows offset = .ok []
    | .ok (some decoded) => ∃ fuel, remaining = fuel + 1 ∧
        MixedFlat.Stream.readBatches limits input fields remaining ordinal rows offset =
          (MixedFlat.Stream.readBatches limits input fields fuel (ordinal + 1)
            (rows + decoded.record.observed.rowCount) decoded.record.range.next).map
            (List.cons decoded.record)

private theorem step_exact {limits : MixedFlat.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {remaining ordinal rows offset : Nat}
    {reply : Except MixedFlat.Stream.Events.Error (Option (Decoded fields))}
    (step : readNext limits input fields remaining ordinal rows offset = reply) :
    StepSpec limits input fields remaining ordinal rows offset reply := by
  cases envelope : readEnvelope limits.observation.ipc input offset with
  | error cause =>
    simp [readNext, envelope, bind, Except.bind, Except.mapError] at step
    subst reply
    exact ⟨.envelope cause, rfl, by simp [MixedFlat.Stream.readBatches, envelope, bind, Except.bind,
      Except.mapError]⟩
  | ok frame =>
    cases frame with
    | eos =>
      by_cases atEnd : offset + 8 = input.len
      · simp [readNext, envelope, atEnd, bind, Except.bind, Except.mapError, pure, Except.pure] at step
        subst reply
        exact ⟨envelope, atEnd, by simp [MixedFlat.Stream.readBatches, envelope, atEnd, bind, Except.bind,
          Except.mapError, pure, Except.pure]⟩
      · simp [readNext, envelope, atEnd, bind, Except.bind, Except.mapError] at step
        subst reply
        exact ⟨.trailingBytes, rfl, by
          simp [MixedFlat.Stream.readBatches, envelope, atEnd, bind, Except.bind, Except.mapError]
          rfl⟩
    | metadata size =>
      cases remaining with
      | zero =>
        simp [readNext, envelope, bind, Except.bind, Except.mapError] at step
        subst reply
        exact ⟨.batchLimit, rfl, by
          simp [MixedFlat.Stream.readBatches, envelope, bind, Except.bind, Except.mapError]
          rfl⟩
      | succ fuel =>
        simp only [readNext, envelope, bind, Except.bind, Except.mapError, Nat.succ_ne_zero,
          ite_false] at step
        split at step
        · rename_i cause record
          change Except.error (.message ordinal offset cause) = reply at step
          subst reply
          exact ⟨cause, rfl, by simp [MixedFlat.Stream.readBatches, envelope, record, bind, Except.bind,
            Except.mapError]⟩
        · rename_i batch record
          simp [pure, Except.pure] at step
          subst reply
          refine ⟨fuel, rfl, ?_⟩
          rw [MixedFlat.Stream.readBatches]
          simp [envelope, record, bind, Except.bind, Except.mapError]
          cases MixedFlat.Stream.readBatches limits input fields fuel (ordinal + 1)
            (rows + batch.observed.rowCount) batch.range.next <;> rfl

theorem readNext_record {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {remaining ordinal rows offset : Nat} {decoded : Decoded fields}
    (step : readNext limits input fields remaining ordinal rows offset = .ok (some decoded)) :
    ∃ fuel, remaining = fuel + 1 ∧
      MixedFlat.Stream.readBatches limits input fields remaining ordinal rows offset =
        (MixedFlat.Stream.readBatches limits input fields fuel (ordinal + 1)
          (rows + decoded.record.observed.rowCount) decoded.record.range.next).map
          (List.cons decoded.record) :=
  step_exact step

private theorem pull_exact (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (remaining ordinal rows offset : Nat) (acc : List (MixedFlat.Events.Batch (schema fields))) :
    let trace := Arrow.Events.BatchReader.read.pull (reader limits) (schema fields)
      (remaining + 1) (.at input fields remaining ordinal rows offset) acc
    match MixedFlat.Stream.readBatches limits input fields remaining ordinal rows offset with
    | .ok records => ∃ events,
        List.Forall₂ (fun record => Agrees (schema fields) record.observed) records events ∧
        trace = ⟨acc.reverse ++ events, .eos⟩
    | .error eagerError => ∃ events available finalOrdinal finalRows finalOffset cause,
        Prefix limits input fields remaining ordinal rows offset events
          available finalOrdinal finalRows finalOffset ∧
        readNext limits input fields available finalOrdinal finalRows finalOffset =
          .error (.message finalOrdinal finalOffset cause) ∧
        eagerError = .batch finalOrdinal cause ∧
        trace = ⟨acc.reverse ++ events, .readError (.message finalOrdinal finalOffset cause)⟩ := by
  induction remaining generalizing ordinal rows offset acc with
  | zero =>
    cases next : readNext limits input fields 0 ordinal rows offset with
    | error error =>
      obtain ⟨cause, rfl, eager⟩ := step_exact next
      simp only [eager]
      exact ⟨[], 0, ordinal, rows, offset, cause, .stop, next, rfl,
        by simp [Arrow.Events.BatchReader.read.pull, reader, next, Except.map]⟩
    | ok reply =>
      cases reply with
      | none =>
        simp only [(step_exact next).2.2]
        exact ⟨[], .nil, by simp [Arrow.Events.BatchReader.read.pull, reader, next, Except.map]⟩
      | some decoded =>
        obtain ⟨_, impossible, _⟩ := step_exact next
        contradiction
  | succ fuel ih =>
    cases next : readNext limits input fields (fuel + 1) ordinal rows offset with
    | error error =>
      obtain ⟨cause, rfl, eager⟩ := step_exact next
      simp only [eager]
      exact ⟨[], fuel + 1, ordinal, rows, offset, cause, .stop, next, rfl,
        by simp [Arrow.Events.BatchReader.read.pull, reader, next, Except.map]⟩
    | ok reply =>
      cases reply with
      | none =>
        simp only [(step_exact next).2.2]
        exact ⟨[], .nil, by simp [Arrow.Events.BatchReader.read.pull, reader, next, Except.map]⟩
      | some decoded =>
        obtain ⟨predecessor, equal, eager⟩ := step_exact next
        have same := Nat.succ.inj equal
        subst predecessor
        let afterRows := rows + decoded.record.observed.rowCount
        let afterOffset := decoded.record.range.next
        have tail := ih (ordinal + 1) afterRows afterOffset (decoded.event :: acc)
        rw [eager]
        cases result : MixedFlat.Stream.readBatches limits input fields fuel (ordinal + 1)
            afterRows afterOffset with
        | error eagerError =>
          rw [result] at tail
          obtain ⟨events, available, finalOrdinal, finalRows, finalOffset, cause,
            delivered, terminal, error, trace⟩ := tail
          simp only [Except.map]
          exact ⟨decoded.event :: events, available, finalOrdinal, finalRows, finalOffset, cause,
            .next next delivered, terminal, error, by
              simpa [Arrow.Events.BatchReader.read.pull, reader, next, Except.map, afterRows,
                afterOffset, List.reverse_cons, List.append_assoc] using trace⟩
        | ok records =>
          rw [result] at tail
          obtain ⟨events, aligned, trace⟩ := tail
          simp only [Except.map]
          exact ⟨decoded.event :: events, .cons decoded.aligned aligned, by
            simpa [Arrow.Events.BatchReader.read.pull, reader, next, Except.map, afterRows,
              afterOffset, List.reverse_cons, List.append_assoc] using trace⟩

private theorem eager_admit (limits : MixedFlat.Limits) (input : KBytes) :
    MixedFlat.Stream.read limits input = (do
      let (fields, start) ← (admit limits input).mapError MixedFlat.Stream.Events.Error.eager
      let batches ← MixedFlat.Stream.readBatches limits input fields limits.observation.ipc.batches 0 0 start
      return ⟨fields, batches⟩) := by
  cases source : input.wf with
  | false =>
    simp [MixedFlat.Stream.read, admit, source, MixedFlat.Stream.Events.Error.eager, bind,
      Except.bind, Except.mapError]
  | true =>
    cases parsed : MixedFlat.Stream.readSchemaFrame limits.observation.ipc input <;>
      simp [MixedFlat.Stream.read, admit, source, parsed, MixedFlat.Stream.Events.Error.eager,
        bind, Except.bind, Except.mapError]

theorem readNext_eos {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {remaining ordinal rows offset : Nat} :
    readNext limits input fields remaining ordinal rows offset = .ok none ↔
      readEnvelope limits.observation.ipc input offset = .ok .eos ∧ offset + 8 = input.len := by
  constructor
  · intro read
    exact ⟨(step_exact read).1, (step_exact read).2.1⟩
  · rintro ⟨envelope, ends⟩
    simp [readNext, envelope, ends, bind, Except.bind, Except.mapError, pure, Except.pure]

theorem readAll_exact (limits : MixedFlat.Limits) (input : KBytes) :
    match admit limits input with
    | .error error =>
        readAll limits input = .error error ∧ MixedFlat.Stream.read limits input = .error error.eager
    | .ok (fields, start) =>
      ∃ trace : Trace (schema fields), readAll limits input = .ok ⟨schema fields, trace⟩ ∧
        match MixedFlat.Stream.read limits input with
        | .ok eager => eager.fields = fields ∧ trace.termination = .eos ∧
            List.Forall₂ (fun record => Agrees (schema fields) record.observed) eager.batches trace.batches
        | .error eagerError =>
          ∃ available ordinal rows offset cause,
            Prefix limits input fields limits.observation.ipc.batches 0 0 start trace.batches
              available ordinal rows offset ∧
            readNext limits input fields available ordinal rows offset =
              .error (.message ordinal offset cause) ∧
            eagerError = .batch ordinal cause ∧ trace.termination = .readError (.message ordinal offset cause) := by
  cases admitted : admit limits input with
  | error error =>
    refine ⟨?_, ?_⟩
    · simp [readAll, Arrow.Events.BatchReader.read, reader, admitted, Except.map]
    · simp [eager_admit, admitted, bind, Except.bind, Except.mapError]
  | ok pair =>
    obtain ⟨fields, start⟩ := pair
    refine ⟨Arrow.Events.BatchReader.read.pull (reader limits) (schema fields)
      (limits.observation.ipc.batches + 1) (.at input fields limits.observation.ipc.batches 0 0 start) [],
      ?_, ?_⟩
    · simp [readAll, Arrow.Events.BatchReader.read, reader, admitted, Except.map]
    · rw [eager_admit, admitted]
      have checked := pull_exact limits input fields limits.observation.ipc.batches 0 0 start []
      cases result : MixedFlat.Stream.readBatches limits input fields limits.observation.ipc.batches 0 0 start with
      | ok records =>
        rw [result] at checked
        obtain ⟨events, aligned, trace⟩ := checked
        simp [bind, Except.bind, Except.mapError, pure, Except.pure, result, trace, aligned]
      | error error =>
        rw [result] at checked
        obtain ⟨events, available, ordinal, rows, offset, cause, delivered, terminal, errorExact, trace⟩ := checked
        simp only [bind, Except.bind, Except.mapError, result, trace, List.reverse_nil, List.nil_append]
        exact ⟨available, ordinal, rows, offset, cause, delivered, terminal, errorExact, rfl⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Events
