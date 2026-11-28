module

public import Silmaril.Formats.Parquet.Timestamp.RoundTrip.Defs
import Silmaril.Formats.Parquet.Timestamp.FromIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Mathlib.Data.List.Basic

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.RoundTrip

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.RoundTrip
open Silmaril.Numeric.Timestamp (Ticks)

private theorem reference_eq {limits : Leaf.Limits} {bound : Leaf.Bound}
    {indices : List Nat} {groups : List (Leaf.Slots bound)}
    (read : indices.mapM (fun index =>
      (Leaf.readGroup limits bound index).mapError (FromIpc.Error.groupReadback index)) = .ok groups) :
    Leaf.Events.referenceGroups limits bound indices = (groups, .eos) := by
  induction indices generalizing groups with
  | nil => simpa [Leaf.Events.referenceGroups, Leaf.Events.referenceGroupsWith] using (Except.ok.inj read)
  | cons index rest ih =>
    rw [List.mapM_cons] at read
    cases result : Leaf.readGroup limits bound index with
    | error cause =>
      rw [result] at read
      contradiction
    | ok slots =>
      rw [result] at read
      change (do
        let following ← rest.mapM (fun i =>
          (Leaf.readGroup limits bound i).mapError (FromIpc.Error.groupReadback i))
        pure (slots :: following)) = .ok groups at read
      cases remaining : rest.mapM (fun i =>
          (Leaf.readGroup limits bound i).mapError (FromIpc.Error.groupReadback i)) with
      | error cause =>
        rw [remaining] at read
        contradiction
      | ok following =>
        rw [remaining] at read
        cases Except.ok.inj read
        have tail := ih remaining
        simp only [Leaf.Events.referenceGroups] at tail
        simp [Leaf.Events.referenceGroups, Leaf.Events.referenceGroupsWith, result, tail]

private theorem binding_eq {source : FromIpc.Source} {bound : Leaf.Bound}
    {groups : List (Leaf.Slots bound)}
    (admitted : FromIpc.descriptor source.stream.binding = .ok source.descriptor)
    (agrees : FromIpc.Internal.ReadbackMatches source bound groups) :
    Leaf.Events.ToIpc.selectedBinding bound = source.stream.binding := by
  obtain ⟨name, nullable, unit, adjusted, _, _, _⟩ := agrees
  obtain ⟨sourceUnit, sourceZone, _⟩ := FromIpc.descriptor_exact admitted
  obtain ⟨outName, outNullable, outUnit, outZone, _⟩ := Leaf.Events.ToIpc.selectedBinding_exact bound
  have sameName := outName.trans name
  have sameNullable : (Leaf.Events.ToIpc.selectedBinding bound).nullable = source.stream.binding.nullable := by
    rw [outNullable, nullable]
    cases source.stream.binding.nullable <;> rfl
  have sameUnit := outUnit.trans ((congrArg ColumnarTimestamp.Parquet.TimeUnit.tickUnit unit).trans sourceUnit)
  have sameZone := outZone.trans (adjusted ▸ sourceZone.symm)
  generalize Leaf.Events.ToIpc.selectedBinding bound = left at sameName sameNullable sameUnit sameZone ⊢
  generalize source.stream.binding = right at sameName sameNullable sameUnit sameZone ⊢
  cases left with
  | mk leftName leftNullable leftMetadata =>
    cases right with
    | mk rightName rightNullable rightMetadata =>
      cases leftMetadata
      cases rightMetadata
      cases sameName
      cases sameNullable
      cases sameUnit
      cases sameZone
      rfl

private theorem stream_eq {left right : Arrow.TimestampStream.Stream}
    (binding : left.binding = right.binding)
    (slots : left.batches.map Arrow.TimestampBatch.Writer.tickCounts =
      right.batches.map Arrow.TimestampBatch.Writer.tickCounts) : left = right := by
  obtain ⟨leftBinding, leftBatches⟩ := left
  obtain ⟨rightBinding, rightBatches⟩ := right
  change leftBinding = rightBinding at binding
  subst rightBinding
  have injective : Function.Injective (@Arrow.TimestampBatch.Writer.tickCounts leftBinding) := by
    unfold Arrow.TimestampBatch.Writer.tickCounts
    apply List.map_injective_iff.mpr
    apply Option.map_injective
    intro a b h
    cases a
    cases b
    cases h
    rfl
  have same : leftBatches = rightBatches := List.map_injective_iff.mpr injective slots
  cases same
  rfl

theorem ipc_roundtrip {inputLimits : Arrow.Limits} {outputLimits : Arrow.ObservationLimits}
    {reverse : FromIpc.Limits} {forward : Leaf.Events.ToIpc.Limits}
    {input output : KBytes} {middle : Bytes}
    (sameSnapshot : forward.snapshot = reverse.snapshot)
    (sameLeaf : forward.leaf = reverse.leaf)
    (toParquet : FromIpc.convert inputLimits reverse input = .ok middle)
    (toIpc : Leaf.Events.ToIpc.convert forward outputLimits middle 1 = .ok output) :
    ∃ stream, Arrow.TimestampStream.read inputLimits input = .ok stream ∧
      ParquetObserves reverse middle stream ∧
      Arrow.TimestampStream.read outputLimits.ipc output = .ok stream := by
  obtain ⟨source, bound, groups, readInput, admitted, opened, decoded, agrees⟩ :=
    FromIpc.convert_readback toParquet
  obtain ⟨other, openedForward, _, result, readOutput, binding, slots⟩ :=
    Leaf.Events.ToIpc.convert_readback toIpc
  have openedOther := (Leaf.Events.ToIpc.openBound_sound openedForward).1
  rw [sameSnapshot, opened] at openedOther
  cases Except.ok.inj openedOther
  have reference := reference_eq decoded
  rw [sameLeaf, reference] at slots
  have sameSlots : result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
      source.stream.batches.map Arrow.TimestampBatch.Writer.tickCounts :=
    slots.trans agrees.2.2.2.2.2.2
  have sameBinding := binding.trans (binding_eq admitted agrees)
  refine ⟨source.stream, readInput, ⟨source.descriptor, bound, groups, admitted, opened, decoded, agrees⟩, ?_⟩
  rw [readOutput, stream_eq sameBinding sameSlots]

end Silmaril.Proofs.Formats.Parquet.Timestamp.RoundTrip
