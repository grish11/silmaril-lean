module

public import Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.TwoBinaryViews.Correctness

public section

namespace Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews

/-- Each view reads back from its own validity, view and data buffers,
with local buffer indices and the same ordered nullable octets. -/
theorem compile_binary_wire {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : List (Option KBytes)} {physical : PhysicalColumn}
    (written : (TwoBinaryViews.Column.binary name nullable values).compile limits rows position = .ok physical) :
    ∃ view, BinaryView.Column.Writer.emitBinary limits.view nullable values = .ok view ∧
      physical = ⟨view.node, some view.buffers.payload.data.size, Writer.viewParts view.buffers⟩ ∧
      ∃ decoded, BinaryView.Column.readBinary limits.view view.node nullable view.buffers = .ok decoded ∧
        decoded.map (Option.map KBytes.toList) = values.map (Option.map KBytes.toList) :=
  Proofs.Formats.Arrow.MixedFlat.TwoBinaryViews.compile_binary_wire written

/-- A checked record binds the exact input field order, an independent count
and descriptor slice for each view, and the original packed buffer bytes. -/
theorem record_wire {limits : MixedFlat.Limits} {input : BatchInput} (record : Record limits input) :
    record.output.metadata.batch.rowCount = input.rowCount ∧
    record.plan.assignment.groups.map Group.field = input.fields ∧
    record.plan.assignment.groups.filterMap Group.count = record.columns.filterMap PhysicalColumn.count ∧
    bindings record.plan record.columns ∧
    Arrow.Writer.PackedWire record.output.body.toList 0 (record.columns.flatMap PhysicalColumn.parts)
      record.output.metadata.batch.buffers :=
  Proofs.Formats.Arrow.MixedFlat.TwoBinaryViews.record_wire record

/-- The existing mixed reader recovers the ordered descriptors, nullable
slots and explicit counts for every record through exact EOS. -/
theorem emit_readback {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧ decoded.fields = fields ∧
      decoded.batches.map StreamWriter.observeBatch = batches.map BatchInput.observe ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame limits.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire limits wire decoded.fields limits.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Arrow.MixedFlat.TwoBinaryViews.emit_readback written

end Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews
