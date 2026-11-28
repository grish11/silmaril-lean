module

public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.StreamWriter.Readback
import Silmaril.Proofs.Formats.Arrow.MixedFlat.StreamWriter.Size

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.StreamWriter

theorem Wire.schema_extent (schema : Schema) :
    (schemaMetadata schema).len = schemaSize schema :=
  Proofs.Formats.Arrow.MixedFlat.StreamWriter.schema_extent schema

/-- Readback preserves the exact ordered fields, every batch's row count
and its ordered nullable slots. BinaryView cells are compared by octets. -/
theorem emit_readback {limits : MixedFlat.Limits} {schema : Schema}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧ decoded.fields = schema.fields ∧
      decoded.batches.map observeBatch = batches.map (BatchInput.observe schema) :=
  Proofs.Formats.Arrow.MixedFlat.StreamWriter.emit_readback written

/-- Schema-only and a zero-row RecordBatch remain distinct observations. -/
theorem emit_batch_rows {limits : MixedFlat.Limits} {schema : Schema}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧ decoded.fields = schema.fields ∧
      decoded.batches.map (fun batch => batch.observed.rowCount) = batches.map BatchInput.rowCount :=
  Proofs.Formats.Arrow.MixedFlat.StreamWriter.emit_batch_rows written

/-- The ordered observations follow checked source ranges through EOS at
the exact end of the carrier. -/
theorem emit_wire {limits : MixedFlat.Limits} {schema : Schema}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    wire.wf = true ∧ ∃ start decoded,
      Stream.readSchemaFrame limits.observation.ipc wire = .ok (schema.fields, start) ∧
      Stream.BatchesWire limits wire schema.fields limits.observation.ipc.batches 0 start decoded ∧
      decoded.map observeBatch = batches.map (BatchInput.observe schema) :=
  Proofs.Formats.Arrow.MixedFlat.StreamWriter.emit_wire written

end Silmaril.Formats.Arrow.MixedFlat.StreamWriter
