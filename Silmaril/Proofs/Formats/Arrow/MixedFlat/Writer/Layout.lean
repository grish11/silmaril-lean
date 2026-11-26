module

public import Silmaril.Formats.Arrow.MixedFlat.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Writer.Readback
import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Writer

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Arrow.MixedFlat
open Silmaril.Formats.Arrow.MixedFlat.Writer
open Silmaril.Formats.Arrow.MetadataWriter.Wire

private theorem appendLen (first second : KBytes) :
    (first ++ second).len = first.len + second.len := rfl

private theorem pairWords {α : Type} (first second : α → Nat) (values : List α) :
    (values.flatMap (fun value => [first value, second value])).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem metadata_extent (batch : RecordBatch) (bodyLength count : Nat) :
    (Wire.metadata batch bodyLength count).len = Wire.metadataSize batch.nodes.length batch.buffers.length := by
  simp only [Wire.metadata, Wire.metadataSize, messagePrefix, words, longs, Arrow.Writer.emitWords_length,
    appendLen, List.length_cons, List.length_nil, pairWords]
  omega

private theorem lengths_of_checked {limits : MixedFlat.Limits} {input : Input}
    (checked : checkInput limits input = .ok ()) :
    input.intValues.length = input.rowCount ∧ input.viewValues.length = input.rowCount := by
  by_cases integer : input.intValues.length = input.rowCount <;>
    by_cases view : input.viewValues.length = input.rowCount
  all_goals
    first
    | exact ⟨integer, view⟩
    | cases budget : Body.checkBudget limits.observation 2 input.rowCount <;>
        simp [checkInput, budget, integer, view, Bind.bind, Except.bind, Except.mapError,
          throw] at checked <;>
        split at checked <;> simp_all <;> split at checked <;> simp_all <;>
        split at checked <;> simp_all

private theorem parts_wf {limits : BinaryView.Column.Limits} {input : Input}
    {view : BinaryView.Column.Writer.Emitted}
    (written : BinaryView.Column.Writer.emitBinary limits input.viewNullable input.viewValues = .ok view) :
    ∀ part ∈ input.parts view.buffers, part.wf = true := by
  have valid := (BinaryView.Column.Writer.emitBinary_layout written).fits.2.2.2.1
  have data : ∀ part ∈ view.buffers.payload.data.toList, part.wf = true := by
    intro part member
    obtain ⟨index, bound, eq⟩ := List.getElem_of_mem member
    rw [← eq]
    simpa using (Array.all_eq_true.mp valid.2.2) index (by simpa using bound)
  have viewPartsWf : ∀ part ∈ viewParts view.buffers, part.wf = true := by
    intro part member
    simp only [viewParts, List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact valid.1
    · exact valid.2.1
    · exact data part member
  have intPartsWf : ∀ part ∈ input.intColumn.emit, part.wf = true := by
    intro part member
    simp only [Input.intColumn, Arrow.Writer.ColumnValues.emit, Arrow.Writer.ColumnValues.encode,
      Arrow.Writer.bufferParts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Arrow.Writer.emitWords_wf _ _
    · exact Arrow.Writer.emitWords_wf _ _
  intro part member
  cases order : input.order <;>
    simp only [Input.parts, order, Order.pair, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_append] at member
  · exact member.elim (intPartsWf part) (viewPartsWf part)
  · exact member.elim (viewPartsWf part) (intPartsWf part)

private theorem serialize_origin {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (serialized : serialize limits input = .ok output) :
    checkInput limits input = .ok () ∧ ∃ view,
      BinaryView.Column.Writer.emitBinary limits.view input.viewNullable input.viewValues = .ok view ∧
      output = encode input view := by
  cases checked : checkInput limits input with
  | error => simp [serialize, checked, Bind.bind, Except.bind] at serialized
  | ok result =>
    cases result
    cases viewWritten : BinaryView.Column.Writer.emitBinary limits.view input.viewNullable input.viewValues with
    | error =>
      simp [serialize, checked, viewWritten, Bind.bind, Except.bind, Except.mapError] at serialized
    | ok view =>
      cases sizes : checkSizes limits view.buffers.payload.data.size
          (input.intColumn.bufferSizes ++ (viewParts view.buffers).map KBytes.len) with
      | error =>
        simp [serialize, checked, viewWritten, sizes, Bind.bind, Except.bind, Except.mapError] at serialized
      | ok result =>
        cases result
        have same : encode input view = output := by
          simpa [serialize, checked, viewWritten, sizes, Bind.bind, Except.bind, Except.mapError,
            Pure.pure, Except.pure] using serialized
        exact ⟨rfl, view, rfl, same.symm⟩

private theorem packed_aligned (start : Nat) (parts : List KBytes) :
    (Arrow.Writer.packBuffers start parts).2.len % 8 = 0 := by
  induction parts generalizing start with
  | nil => rfl
  | cons first rest ih =>
    let size := first.len + Arrow.Writer.padding first.len
    have alignHead : size % 8 = 0 := Arrow.Writer.padding_aligned first.len
    let next := start + first.len + Arrow.Writer.padding first.len
    have alignTail := ih next
    change (first.len + (Arrow.Writer.padding first.len +
      (Arrow.Writer.packBuffers next rest).2.len)) % 8 = 0
    omega

theorem emit_layout {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (written : emit limits input = .ok output) : Layout limits input output := by
  obtain ⟨checked, view, viewWritten, rfl⟩ := serialize_origin (emit_checked written).1
  have physical := BinaryView.Column.Writer.emitBinary_layout viewWritten
  exact ⟨lengths_of_checked checked, rfl,
    by simp only [encode, physical.node, Input.intNode, Input.intColumn,
      Arrow.Writer.ColumnValues.length, Arrow.Writer.ColumnValues.nullCount],
    by simp only [encode, physical.variadicCount], rfl, packed_aligned _ _,
    metadata_extent _ _ _, view, viewWritten, Arrow.Writer.packBuffers_exact _ (parts_wf viewWritten)⟩

private theorem primitive_count {rows : Nat} (group : Group rows)
    (integer : group.field.kind = .primitive .int32) : group.count = none := by
  have kind := group.countKind
  cases count : group.count <;> simp_all [Kind.isView]

private theorem descriptor_split {rows width : Nat} {first second : Group rows}
    {buffers : List Buffer} (joined : first.buffers ++ second.buffers = buffers)
    (firstWidth : first.buffers.length = width) :
    [first.buffers, second.buffers] = [buffers.take width, buffers.drop width] := by
  rw [← joined, ← firstWidth, List.take_left, List.drop_left]

theorem emit_partition {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (written : emit limits input = .ok output) :
    ∃ plan, MixedFlat.bindBatch limits input.fields output.metadata output.body = .ok plan ∧
      let count := BinaryView.Column.Writer.dataCount
        (BinaryView.Column.Writer.longBytes KBytes.len input.viewValues)
      let width := if input.order = .intFirst then 2 else 2 + count
      plan.assignment.groups.map Group.count = input.order.pair none (some count) ∧
        plan.assignment.groups.map Group.buffers =
          [output.metadata.batch.buffers.take width, output.metadata.batch.buffers.drop width] := by
  obtain ⟨plan, bound, fields, _, counts, buffers⟩ := emit_assignment written
  have length : plan.assignment.groups.length = 2 := by
    have length := congrArg List.length fields
    cases order : input.order <;> simpa [Input.fields, Order.pair, order] using length
  let first := plan.assignment.groups[0]'(by omega)
  let second := plan.assignment.groups[1]'(by omega)
  have groups : plan.assignment.groups = [first, second] :=
    List.eq_getElem_of_length_eq_two _ length
  have joined : first.buffers ++ second.buffers = output.metadata.batch.buffers := by
    simpa [groups] using buffers
  let count := BinaryView.Column.Writer.dataCount
    (BinaryView.Column.Writer.longBytes KBytes.len input.viewValues)
  have countVector : [first, second].filterMap Group.count = [count] := by
    rw [← groups, counts]
    exact (emit_layout written).counts
  refine ⟨plan, bound, ?_⟩
  change _ = input.order.pair none (some count) ∧
    _ = [output.metadata.batch.buffers.take (if input.order = .intFirst then 2 else 2 + count),
      output.metadata.batch.buffers.drop (if input.order = .intFirst then 2 else 2 + count)]
  rw [groups] at fields ⊢
  cases order : input.order with
  | intFirst =>
    have pair : first.field = input.intField ∧ second.field = input.viewField := by
      simpa [Input.fields, Order.pair, order] using fields
    have kind : first.field.kind = .primitive .int32 := by rw [pair.1]; rfl
    have noCount := primitive_count first kind
    have viewCount : second.count = some count := by
      cases found : second.count with
      | none => simp [noCount, found] at countVector
      | some actual => simpa [noCount, found] using countVector
    have width : first.buffers.length = 2 := by
      simpa [kind, noCount, Kind.baseBuffers] using first.width
    exact ⟨by simp [Order.pair, noCount, viewCount], descriptor_split joined width⟩
  | viewFirst =>
    have pair : first.field = input.viewField ∧ second.field = input.intField := by
      simpa [Input.fields, Order.pair, order] using fields
    have firstKind : first.field.kind = .view .binary := by rw [pair.1]; rfl
    have secondKind : second.field.kind = .primitive .int32 := by rw [pair.2]; rfl
    have noCount := primitive_count second secondKind
    have viewCount : first.count = some count := by
      cases found : first.count with
      | none => simp [noCount, found] at countVector
      | some actual => simpa [noCount, found] using countVector
    have width : first.buffers.length = 2 + count := by
      simpa [firstKind, viewCount, Kind.baseBuffers] using first.width
    exact ⟨by simp [Order.pair, viewCount, noCount], descriptor_split joined width⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Writer
