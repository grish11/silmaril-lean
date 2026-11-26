module

public import Silmaril.Formats.Arrow.MixedFlat.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Writer.Layout
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Writer.Readback

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Writer

theorem Wire.metadata_extent (batch : RecordBatch) (bodyLength count : Nat) :
    (metadata batch bodyLength count).len = metadataSize batch.nodes.length batch.buffers.length :=
  Proofs.Formats.Arrow.MixedFlat.Writer.metadata_extent batch bodyLength count

/-- The nodes and count are exact, and each descriptor selects the packed
physical bytes for its corresponding input buffer. -/
theorem emit_layout {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (written : emit limits input = .ok output) : Layout limits input output :=
  Proofs.Formats.Arrow.MixedFlat.Writer.emit_layout written

/-- The reader's assignment exhausts the fields, nodes, view counts and
descriptors in the input's selected schema order. -/
theorem emit_assignment {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (written : emit limits input = .ok output) :
    ∃ plan, MixedFlat.bindBatch limits input.fields output.metadata output.body = .ok plan ∧
      plan.assignment.groups.map Group.field = input.fields ∧
      plan.assignment.groups.map Group.node = output.metadata.batch.nodes ∧
      plan.assignment.groups.filterMap Group.count = output.metadata.counts ∧
      plan.assignment.groups.flatMap Group.buffers = output.metadata.batch.buffers :=
  Proofs.Formats.Arrow.MixedFlat.Writer.emit_assignment written

/-- The Int32 group owns two descriptors and no count word. The view group
owns two descriptors plus its count, with an explicit count of zero for
inline-only or empty values. The first group's width fixes the split. -/
theorem emit_partition {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (written : emit limits input = .ok output) :
    ∃ plan, MixedFlat.bindBatch limits input.fields output.metadata output.body = .ok plan ∧
      let count := BinaryView.Column.Writer.dataCount
        (BinaryView.Column.Writer.longBytes KBytes.len input.viewValues)
      let width := if input.order = .intFirst then 2 else 2 + count
      plan.assignment.groups.map Group.count = input.order.pair none (some count) ∧
        plan.assignment.groups.map Group.buffers =
          [output.metadata.batch.buffers.take width, output.metadata.batch.buffers.drop width] :=
  Proofs.Formats.Arrow.MixedFlat.Writer.emit_partition written

/-- The checked metadata parser recovers the exact descriptors. The body
reader recovers the declared row count, fields and ordered nullable values. -/
theorem emit_readback {limits : MixedFlat.Limits} {input : Input} {output : Emitted}
    (written : emit limits input = .ok output) :
    MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers
      input.fields output.metadataBytes = .ok output.metadata ∧
    ∃ values, MixedFlat.readParsed limits input.fields output.metadata output.body = .ok values ∧
      values.rowCount = input.rowCount ∧ observeColumns values.columns = some input.observe :=
  Proofs.Formats.Arrow.MixedFlat.Writer.emit_readback written

end Silmaril.Formats.Arrow.MixedFlat.Writer
