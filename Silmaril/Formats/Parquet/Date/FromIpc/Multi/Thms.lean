module

public import Silmaril.Formats.Parquet.Date.FromIpc.Multi.Defs
import Silmaril.Proofs.Formats.Parquet.Date.FromIpc.Multi.Correctness

public section

namespace Silmaril.Formats.Parquet.Date.FromIpc.Multi

open Silmaril.Formats.Parquet.Date.FromIpc.Multi.Internal

/-- A planned group's chunk starts after exactly the preceding measured pages. -/
theorem placements_at (start : Nat) {groups : List Group} {index : Nat} {group : Group}
    (found : groups[index]? = some group) :
    let offset := start + ((groups.take index).map (·.size)).sum
    (placements start groups)[index]? = some (group.rows, ⟨offset, offset + group.size⟩) :=
  Proofs.Formats.Parquet.Date.FromIpc.Multi.placements_at start found

/-- Admission counts explicit batches, including empty batches, before preparing any page. -/
theorem budget_exact {limits : Limits} {field : Arrow.DateStream.Field} {batches : Batches}
    (checked : checkBudget limits field batches = .ok ()) :
    batches ≠ [] ∧ batches.length ≤ limits.maxGroups ∧
      batches.length ≤ limits.writer.footer.compact.maxCollectionSize ∧
      totalRows batches ≤ limits.maxTotalRows ∧ totalRows batches < 2^63 ∧
      0 < limits.writer.maxColumns ∧ 2 ≤ limits.writer.footer.compact.maxCollectionSize ∧
      field.name.utf8ByteSize ≤ limits.writer.footer.compact.maxBinaryBytes :=
  Proofs.Formats.Parquet.Date.FromIpc.Multi.budget_exact checked

/-- The plan measures every page in order, with the original batch row counts.
Its footer fits both the footer cap and the residual whole-file cap. -/
theorem preflight_exact {limits : Limits} {field : Arrow.DateStream.Field} {batches : Batches}
    {plan : Plan} (planned : preflight limits field batches = .ok plan) :
    checkBudget limits field batches = .ok () ∧
    plan.groups.map (·.rows) = batches.map List.length ∧
    (∀ group ∈ plan.groups, 0 < group.size ∧
      FlatInt32Writer.measuredPage limits.writer.page group.input = .ok group.size) ∧
    FlatInt32Writer.Compact.encodeGroups .date (footerLimit limits plan.dataStop)
      [schemaIndex field] (groupIndices field plan.groups) = .ok plan.footer ∧
    plan.footer.length ≤ footerLimit limits plan.dataStop ∧ plan.fileSize ≤ fileLimit limits :=
  Proofs.Formats.Parquet.Date.FromIpc.Multi.preflight_exact planned

/-- Materialized bytes have exactly the preflight extent. -/
theorem emit_extent {limits : Limits} {plan : Plan} {wire : Bytes}
    (written : emit limits plan = .ok wire) : wire.length = plan.fileSize :=
  Proofs.Formats.Parquet.Date.FromIpc.Multi.emit_extent written

/-- A completed file comes from the checked EOS source and exact output plan.
The retained DATE snapshot agrees in schema, group count, footer total and batch order. -/
theorem convert_readback {inputLimits : Arrow.Limits} {writerLimits : Limits} {readbackLimits : Date.Limits}
    {input : KBytes} {wire : Bytes} (written : convert inputLimits writerLimits readbackLimits input = .ok wire) :
    ∃ source plan checked groups,
      Arrow.DateStream.read inputLimits input = .ok source ∧ source.field.unit = .day ∧
      preflight writerLimits source.field source.batches = .ok plan ∧
      wire.length = plan.fileSize ∧ Date.openChecked readbackLimits wire = .ok checked ∧
      readGroups readbackLimits checked = .ok groups ∧ Matches checked groups source.field source.batches :=
  Proofs.Formats.Parquet.Date.FromIpc.Multi.convert_readback written

/-- Each admitted batch has its own indexed group, with the exact nullable signed
days in the same order. A zero-row batch gives a group with zero slots. -/
theorem readback_at {limits : Date.Limits} {checked : Date.Checked} {groups : List Date.RowGroup}
    {field : Arrow.DateStream.Field} {batches : Batches}
    (read : readGroups limits checked = .ok groups)
    (agrees : Matches checked groups field batches) (index : Fin batches.length) :
    ∃ group, checked.readGroup limits index.val = .ok group ∧
      group.rowCount = batches[index.val].length ∧ group.civilSlots = batches[index.val] ∧
      group.date32Slots = batches[index.val].map (fun slot => slot.bind DateInterop.Date32.ofCivil?) :=
  Proofs.Formats.Parquet.Date.FromIpc.Multi.readback_at read agrees index

/-- A source failure, including an error after earlier batches, takes precedence over output caps. -/
theorem convert_readError {inputLimits : Arrow.Limits} {writerLimits : Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {cause : Arrow.DateStream.Error}
    (failed : Arrow.DateStream.read inputLimits input = .error cause) :
    convert inputLimits writerLimits readbackLimits input = .error (.source (.reader cause)) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

/-- A Date32 schema through EOS with no record batch returns `batchCount 0`. -/
theorem convert_noBatches {inputLimits : Arrow.Limits} {writerLimits : Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {source : Arrow.DateStream.Stream}
    (read : Arrow.DateStream.read inputLimits input = .ok source)
    (day : source.field.unit = .day) (empty : source.batches = []) :
    convert inputLimits writerLimits readbackLimits input = .error (.source (.batchCount 0)) := by
  simp [convert, read, day, empty, preflight, checkBudget, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.FromIpc.Multi
