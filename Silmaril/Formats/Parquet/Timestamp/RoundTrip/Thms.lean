module

public import Silmaril.Formats.Parquet.Timestamp.RoundTrip.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.RoundTrip.Composition

public section

namespace Silmaril.Formats.Parquet.Timestamp.RoundTrip

/-- For a checked one-field V5 TIMESTAMP stream in millis, micros or nanos
with local or exact UTC interpretation, the two successful conversions
preserve the exact decoded field and ordered nullable ticks. Every explicit
batch, including an empty batch, corresponds to a footer group. A
schema-only stream has no groups. Only the intermediate snapshot and leaf
readback settings are matched. Source, file admission and sink caps may differ. -/
theorem ipc_roundtrip {inputLimits : Arrow.Limits} {outputLimits : Arrow.ObservationLimits}
    {reverse : FromIpc.Limits} {forward : Leaf.Events.ToIpc.Limits}
    {input output : KBytes} {middle : Bytes}
    (sameSnapshot : forward.snapshot = reverse.snapshot)
    (sameLeaf : forward.leaf = reverse.leaf)
    (toParquet : FromIpc.convert inputLimits reverse input = .ok middle)
    (toIpc : Leaf.Events.ToIpc.convert forward outputLimits middle 1 = .ok output) :
    ∃ stream, Arrow.TimestampStream.read inputLimits input = .ok stream ∧
      ParquetObserves reverse middle stream ∧
      Arrow.TimestampStream.read outputLimits.ipc output = .ok stream :=
  Proofs.Formats.Parquet.Timestamp.RoundTrip.ipc_roundtrip sameSnapshot sameLeaf toParquet toIpc

end Silmaril.Formats.Parquet.Timestamp.RoundTrip
