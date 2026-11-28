module

public import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.TimestampStream.Writer

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.TimestampStream.Writer
open Silmaril.Formats.Arrow.MetadataWriter.Wire
open Silmaril.Numeric.Timestamp (TickUnit)

private theorem append_length (a b : KBytes) : (a ++ b).len = a.len + b.len := rfl
private theorem zeros_length (n : Nat) : (KBytes.zeros n).len = n := rfl

private theorem timestampType_length (unit : TickUnit) (offset : Option Nat) :
    (Internal.timestampType unit offset).len = 20 := by
  simp [Internal.timestampType, words, Arrow.Writer.emitWords_length]

private theorem fieldFragment_length (name : String) (nullable : Bool)
    (unit : TickUnit) (offset : Option Nat) :
    (fieldFragment name nullable 10 (Internal.timestampType unit offset)).len = Internal.nameFragmentSize name := by
  have nameSize : name.toByteArray.data.toList.length = name.utf8ByteSize := rfl
  simp only [Internal.nameFragmentSize, fieldFragment, pad, words, Arrow.Writer.emitWords_length,
    append_length, zeros_length, timestampType_length, List.length_cons, List.length_nil,
    List.length_map, nameSize]
  have size : 4 * 7 + (20 + (4 * 1 + (1 * name.utf8ByteSize + 1))) = 53 + name.utf8ByteSize := by omega
  rw [size]

private theorem utcString_length : Internal.utcString.len = 8 := by
  simp [Internal.utcString, words, Arrow.Writer.emitWords_length]

private theorem timestampField_length (binding : TimestampBatch.Binding) :
    (Internal.timestampField binding).len =
      Internal.nameFragmentSize binding.name + (if binding.metadata.timezone == some "UTC" then 8 else 0) := by
  simp only [Internal.timestampField, append_length, fieldFragment_length]
  split
  · simp [utcString_length]
  · rfl

theorem schemaMetadata_size (binding : TimestampBatch.Binding) :
    (Internal.schemaMetadata binding).len = Internal.schemaSize binding := by
  simp only [Internal.schemaMetadata, Internal.schemaSize, messagePrefix, schemaPayloadOf, fieldOffsets,
    words, longs, Arrow.Writer.emitWords_length, append_length, zeros_length, timestampField_length,
    List.length_cons, List.length_nil, List.foldr_cons, List.foldr_nil]
  change 48 + (24 + (0 + ((_ + _) + 0))) = _
  omega

private theorem descriptor_eq {first second : TimestampBatch.Binding}
    (same : descriptor first = descriptor second) : first = second := by
  obtain ⟨firstName, firstNullable, ⟨firstUnit, firstZone⟩⟩ := first
  obtain ⟨secondName, secondNullable, ⟨secondUnit, secondZone⟩⟩ := second
  simp [descriptor] at same
  obtain ⟨rfl, rfl, rfl, rfl⟩ := same
  rfl

theorem emitSchema_readback {limits : Limits} {binding : TimestampBatch.Binding} {frame : KBytes}
    (written : emitSchema limits binding = .ok frame) :
    TimestampStream.readSchema limits frame = .ok (binding, frame.len) := by
  cases serialized : Internal.serializeSchema limits binding with
  | error reason => simp [emitSchema, serialized, Bind.bind, Except.bind] at written
  | ok bytes =>
    cases observed : TimestampStream.readSchema limits bytes with
    | error reason => simp [emitSchema, serialized, observed, Bind.bind, Except.bind, Except.mapError] at written
    | ok result =>
      obtain ⟨read, next⟩ := result
      by_cases exactRead : next = bytes.len ∧ descriptor read = descriptor binding
      · have output : bytes = frame := by
          simpa [emitSchema, serialized, observed, exactRead, Bind.bind, Except.bind, Except.mapError,
            Pure.pure, Except.pure] using written
        cases output
        rw [observed, descriptor_eq exactRead.2, exactRead.1]
      · simp [emitSchema, serialized, observed, exactRead, Bind.bind, Except.bind, Except.mapError] at written

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem serialize_wire {limits : ObservationLimits} {binding : TimestampBatch.Binding}
    {batches : List (TimestampBatch.Column binding)} {wire : KBytes}
    (serialized : Internal.serialize limits binding batches = .ok wire) :
    ∃ schema records, emitSchema limits.ipc binding = .ok schema ∧
      (batches.zipIdx.mapM fun (slots, index) => Internal.emitRecord limits.ipc binding slots index) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos := by
  unfold Internal.serialize at serialized
  split at serialized
  · contradiction
  · obtain ⟨_, _, ready⟩ := bind_ok serialized
    obtain ⟨schema, schemaOk, ready⟩ := bind_ok ready
    obtain ⟨records, recordsOk, ready⟩ := bind_ok ready
    exact ⟨schema, records, schemaOk, recordsOk, (Except.ok.inj ready).symm⟩

private theorem emit_checked {limits : ObservationLimits} {binding : TimestampBatch.Binding}
    {batches : List (TimestampBatch.Column binding)} {wire : KBytes}
    (written : emit limits binding batches = .ok wire) :
    Internal.serialize limits binding batches = .ok wire ∧
      ∃ result, TimestampStream.read limits.ipc wire = .ok result ∧ result.binding = binding ∧
        result.batches.map TimestampBatch.Writer.tickCounts = batches.map TimestampBatch.Writer.tickCounts := by
  cases serialized : Internal.serialize limits binding batches with
  | error reason => simp [emit, serialized, Bind.bind, Except.bind] at written
  | ok actual =>
    cases observed : TimestampStream.read limits.ipc actual with
    | error reason => simp [emit, serialized, observed, Bind.bind, Except.bind, Except.mapError] at written
    | ok result =>
      by_cases exactRead : descriptor result.binding = descriptor binding ∧
          result.batches.map TimestampBatch.Writer.tickCounts = batches.map TimestampBatch.Writer.tickCounts
      · have output : actual = wire := by
          simpa [emit, serialized, observed, exactRead, Bind.bind, Except.bind, Except.mapError,
            Pure.pure, Except.pure] using written
        cases output
        exact ⟨rfl, result, observed, descriptor_eq exactRead.1, exactRead.2⟩
      · simp [emit, serialized, observed, exactRead, Bind.bind, Except.bind, Except.mapError] at written

theorem emit_wire {limits : ObservationLimits} {binding : TimestampBatch.Binding}
    {batches : List (TimestampBatch.Column binding)} {wire : KBytes}
    (written : emit limits binding batches = .ok wire) :
    ∃ schema records, emitSchema limits.ipc binding = .ok schema ∧
      (batches.zipIdx.mapM fun (slots, index) => Internal.emitRecord limits.ipc binding slots index) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos :=
  serialize_wire (emit_checked written).1

theorem emit_readback {limits : ObservationLimits} {binding : TimestampBatch.Binding}
    {batches : List (TimestampBatch.Column binding)} {wire : KBytes}
    (written : emit limits binding batches = .ok wire) :
    ∃ result, TimestampStream.read limits.ipc wire = .ok result ∧ result.binding = binding ∧
      result.batches.map TimestampBatch.Writer.tickCounts = batches.map TimestampBatch.Writer.tickCounts :=
  (emit_checked written).2

end Silmaril.Proofs.Formats.Arrow.TimestampStream.Writer
