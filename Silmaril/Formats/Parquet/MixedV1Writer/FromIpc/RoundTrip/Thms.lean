module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.Correctness

/-! Observational round trip through real nonlegacy mixed Parquet bytes. -/

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip

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

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip
