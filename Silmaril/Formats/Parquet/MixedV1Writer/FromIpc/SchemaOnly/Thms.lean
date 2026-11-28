module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.Correctness

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly

open Silmaril.Formats.Relational.NamedTable

/-- The parsed footer is exact and the checked source has no groups. -/
theorem emit_checked {limits : MixedV1Writer.Multi.Limits} {descriptor : MixedIpc.Descriptor}
    {output : MixedV1Writer.Multi.Encoded} (written : emit limits descriptor = .ok output) :
    output.groups = [] ∧ output.footer.start = 4 ∧
    Footer.readFooter limits.writer.footer output.bytes = .ok (output.footer, metadata descriptor) ∧
    ∃ checked : Int32ByteArrayGroup.Checked (field descriptor.integer) (field descriptor.binary),
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes
        (field descriptor.integer) (field descriptor.binary) = .ok checked ∧
      checked.snapshot.groupCount = 0 :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.emit_checked written

/-- Successful conversion admits the exact descriptor and zero IPC batches. -/
theorem convert_checked {source : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {input : KBytes} {output : MixedV1Writer.Multi.Encoded}
    (written : convert source sink input = .ok output) :
    ∃ descriptor, MixedIpc.read source input = .ok ⟨descriptor, []⟩ ∧
      emit sink descriptor = .ok output :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.convert_checked written

/-- Reject a real RecordBatch even if it has zero rows. -/
theorem convert_batchCount {source : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {input : KBytes} {observed : MixedIpc.Prepared}
    (read : MixedIpc.read source input = .ok observed) (nonempty : observed.batches ≠ []) :
    convert source sink input = .error (.batchCount observed.batches.length) :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.convert_batchCount read nonempty

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly
