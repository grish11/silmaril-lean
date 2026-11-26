module

public import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.TimestampStream.Writer.RoundTrip

public section

namespace Silmaril.Formats.Arrow.TimestampStream.Writer

/-- The preflight size equals the actual padded Schema metadata extent. -/
theorem schemaMetadata_size (binding : TimestampBatch.Binding) :
    (Internal.schemaMetadata binding).len = Internal.schemaSize binding :=
  Proofs.Formats.Arrow.TimestampStream.Writer.schemaMetadata_size binding

/-- The Schema frame reads back to the exact descriptor and consumes the full frame. -/
theorem emitSchema_readback {limits : Limits} {binding : TimestampBatch.Binding} {frame : KBytes}
    (written : emitSchema limits binding = .ok frame) :
    TimestampStream.readSchema limits frame = .ok (binding, frame.len) :=
  Proofs.Formats.Arrow.TimestampStream.Writer.emitSchema_readback written

/-- The stream is the certified native Schema and the records in input order,
terminated by the existing exact EOS marker. -/
theorem emit_wire {limits : ObservationLimits} {binding : TimestampBatch.Binding}
    {batches : List (TimestampBatch.Column binding)} {wire : KBytes}
    (written : emit limits binding batches = .ok wire) :
    ∃ schema records, emitSchema limits.ipc binding = .ok schema ∧
      (batches.zipIdx.mapM fun (slots, index) => Internal.emitRecord limits.ipc binding slots index) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos :=
  Proofs.Formats.Arrow.TimestampStream.Writer.emit_wire written

/-- The checked reader recovers the exact descriptor and ordered nullable
signed ticks with the input batch boundaries. -/
theorem emit_readback {limits : ObservationLimits} {binding : TimestampBatch.Binding}
    {batches : List (TimestampBatch.Column binding)} {wire : KBytes}
    (written : emit limits binding batches = .ok wire) :
    ∃ result, TimestampStream.read limits.ipc wire = .ok result ∧ result.binding = binding ∧
      result.batches.map TimestampBatch.Writer.tickCounts = batches.map TimestampBatch.Writer.tickCounts :=
  Proofs.Formats.Arrow.TimestampStream.Writer.emit_readback written

end Silmaril.Formats.Arrow.TimestampStream.Writer
