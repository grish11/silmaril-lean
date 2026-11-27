module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.Correctness

/-! Observational round trip through real nonlegacy mixed Parquet bytes. -/

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable

/-- The returned checked IPC observation has exactly the original descriptor and
ordered batches, including empty batches. Both conversions must succeed. The
reverse reader uses the same group limits as writer certification and may impose
its own aggregate row cap. The returned carrier obeys its own IPC byte cap. -/
theorem read_roundTrip {source returned : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {reverse : File.Limits} {input output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    {observed : MixedIpc.Prepared}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convert source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (backward : ToIpc.convert reverse returned.mixed parquet.bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.read_roundTrip original forward groupLimits backward carrier

/-- Both native conversions retain the exact descriptor and every batch through EOS.
The original descriptor also fixes the actual Parquet leaf and chunk vectors.
Use the same footer parser policy for writing and reopening, and the same group
limits for certification and reopening. The reverse file-row cap and returned
IPC carrier cap are independent. -/
theorem read_roundTripOrdered {source returned : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {reverse : File.Limits} {input output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    {observed : MixedIpc.Prepared}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convertOrdered source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (footerLimits : reverse.group.snapshot.footer = sink.writer.footer)
    (backward : ToIpc.convertOrdered reverse returned.mixed parquet.bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed ∧
      ∃ parsed : Footer.Metadata,
        Footer.readFooter sink.writer.footer parquet.bytes = .ok (parquet.footer, parsed) ∧
        parsed.schema = FlatInt32Writer.Compact.schemaRoot 2 ::
          (physicalOrder observed.descriptor).columns
            (MixedV1Writer.columnIndex (field observed.descriptor.integer) ⟨0, 0⟩).schema
            (MixedV1Writer.byteSchema (MixedV1Writer.columnIndex (field observed.descriptor.binary) ⟨0, 0⟩)) ∧
        parsed.rowGroups.map Footer.RowGroup.columns =
          parquet.groups.map (fun pages => (physicalOrder observed.descriptor).columns
            (pages.index.ints.metadata pages.index.rows)
            (MixedV1Writer.byteChunk pages.index.octets pages.index.rows)) :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.read_roundTripOrdered
    original forward groupLimits footerLimits backward carrier

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip
