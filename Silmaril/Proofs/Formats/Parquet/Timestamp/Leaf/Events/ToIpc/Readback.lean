module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Arrow.TimestampStream.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

theorem openBound_sound {limits : Limits} {input : Bytes} {ordinal : Nat} {bound : Leaf.Bound}
    (opened : openBound limits input ordinal = .ok bound) :
    Leaf.openLeaf limits.snapshot input ordinal = .ok bound ∧ input.length ≤ limits.maxFileBytes ∧
      bound.snapshot.groupCount ≤ limits.maxGroups ∧
      bound.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows := by
  by_cases bytes : limits.maxFileBytes < input.length
  · simp [openBound, bytes] at opened
  · cases selected : Leaf.openLeaf limits.snapshot input ordinal with
    | error reason => simp [openBound, bytes, selected, Bind.bind, Except.bind, Except.mapError] at opened
    | ok candidate =>
      by_cases groups : limits.maxGroups < candidate.snapshot.groupCount
      · simp [openBound, bytes, selected, groups, Bind.bind, Except.bind, Except.mapError] at opened
      · by_cases rows : limits.maxTotalRows < candidate.snapshot.metadata.numRows.toNat
        · simp [openBound, bytes, selected, groups, rows, Bind.bind, Except.bind, Except.mapError] at opened
        · simp [openBound, bytes, selected, groups, rows, Bind.bind, Except.bind, Except.mapError] at opened
          cases opened
          exact ⟨rfl, Nat.le_of_not_gt bytes, Nat.le_of_not_gt groups, Nat.le_of_not_gt rows⟩

theorem selectedBinding_exact (bound : Leaf.Bound) :
    (selectedBinding bound).name = bound.binding.leaf.name ∧
      (selectedBinding bound).nullable = (bound.binding.leaf.repetition == some .optional) ∧
      (selectedBinding bound).metadata.unit = bound.binding.descriptor.unit.tickUnit ∧
      (selectedBinding bound).metadata.timezone = (if bound.binding.descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      (selectedBinding bound).metadata.kind = bound.binding.descriptor.kind :=
  ⟨rfl, rfl, Leaf.Events.metadata_exact bound⟩

theorem emit_trace_error (limits : Arrow.ObservationLimits) {schema : Scan.Schema String Leaf.Events.Kind}
    {trace : Arrow.Events.Trace schema Leaf.Events.Cell Leaf.Events.Error} {cause : Leaf.Events.Error}
    (failed : trace.termination = .readError cause) :
    emit limits (.ok ⟨schema, trace⟩) = .error (.source cause) := by
  simp [emit, failed]

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

theorem emit_readback {limits : Arrow.ObservationLimits} {schema : Scan.Schema String Leaf.Events.Kind}
    {trace : Arrow.Events.Trace schema Leaf.Events.Cell Leaf.Events.Error} {wire : KBytes}
    (one : schema.width = 1) (ended : trace.termination = .eos)
    (written : emit limits (.ok ⟨schema, trace⟩) = .ok wire) :
    let column : Fin schema.width := ⟨0, by omega⟩
    ∃ result, Arrow.TimestampStream.read limits.ipc wire = .ok result ∧
      result.binding = bindingAt schema column ∧
      result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
        (batchesAt trace column).map Arrow.TimestampBatch.Writer.tickCounts := by
  let column : Fin schema.width := ⟨0, by omega⟩
  have encoded : (Arrow.TimestampStream.Writer.emit limits (bindingAt schema column)
      (batchesAt trace column)).mapError Leaf.Events.ToIpc.Error.writer = .ok wire := by
    simpa [emit, ended, one, column] using written
  exact Arrow.TimestampStream.Writer.emit_readback (mapError_ok encoded)

private theorem boundEvents_eq_readAll {limits : Snapshot.Limits} {input : Bytes} {ordinal : Nat}
    {bound : Leaf.Bound} (opened : Leaf.openLeaf limits input ordinal = .ok bound) (leaf : Leaf.Limits) :
    boundEvents leaf bound = Leaf.Events.readAll limits leaf ordinal input := by
  simp [boundEvents, Leaf.Events.readAll, Leaf.Events.openSource, opened, Except.mapError, Except.map]

theorem convert_first_error {inputLimits : Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal index : Nat} {bound : Leaf.Bound}
    {before after : List Nat} {groups : List (Leaf.Slots bound)} {cause : Leaf.Error}
    (opened : openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Leaf.readGroup inputLimits.leaf bound) = .ok groups)
    (failed : Leaf.readGroup inputLimits.leaf bound index = .error cause) :
    convert inputLimits outputLimits input ordinal = .error (.source (.groupFailure index cause)) := by
  have selected := (openBound_sound opened).1
  have read := (boundEvents_eq_readAll selected inputLimits.leaf).trans
    (Leaf.Events.readAll_first_error selected split earlier failed)
  simp [convert, opened, read, emit, Bind.bind, Except.bind]

private theorem batchesAt_reference (bound : Leaf.Bound) (slots : List (Leaf.Slots bound))
    (termination : Arrow.Events.Termination Leaf.Events.Error) (column : Fin (Leaf.Events.schema bound).width) :
    (batchesAt ⟨slots.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), termination⟩ column).map
        Arrow.TimestampBatch.Writer.tickCounts =
      slots.map (List.map (Option.map Ticks.ticks)) := by
  induction slots with
  | nil => rfl
  | cons group rest ih =>
    exact congrArg₂ List.cons (Leaf.Events.batch_slots bound group column).2 ih

theorem convert_readback {inputLimits : Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Leaf.Bound, openBound inputLimits input ordinal = .ok bound ∧
      let reference := Leaf.Events.referenceGroups inputLimits.leaf bound (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) := by
  cases opened : openBound inputLimits input ordinal with
  | error reason => simp [convert, opened, Bind.bind, Except.bind] at written
  | ok bound =>
    let reference := Leaf.Events.referenceGroups inputLimits.leaf bound (List.range bound.snapshot.groupCount)
    let trace : Arrow.Events.Trace (Leaf.Events.schema bound) Leaf.Events.Cell Leaf.Events.Error :=
      ⟨reference.1.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), reference.2⟩
    have selected := (openBound_sound opened).1
    have events : boundEvents inputLimits.leaf bound = .ok ⟨Leaf.Events.schema bound, trace⟩ :=
      (boundEvents_eq_readAll selected inputLimits.leaf).trans (Leaf.Events.readAll_reference selected)
    have emitted : emit outputLimits (.ok ⟨Leaf.Events.schema bound, trace⟩) = .ok wire := by
      simpa [convert, opened, events, Bind.bind, Except.bind] using written
    cases ended : reference.2 with
    | eos =>
      have width : (Leaf.Events.schema bound).width = 1 := rfl
      obtain ⟨result, read, binding, batches⟩ := emit_readback width ended emitted
      refine ⟨bound, rfl, ended, result, read, binding, ?_⟩
      exact batches.trans (batchesAt_reference bound reference.1 reference.2 ⟨0, Nat.zero_lt_one⟩)
    | closed => simp [emit, trace, ended] at emitted
    | readError cause => simp [emit, trace, ended] at emitted
    | closeError cause => simp [emit, trace, ended] at emitted

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
