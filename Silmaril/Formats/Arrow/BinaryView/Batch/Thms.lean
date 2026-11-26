module

public import Silmaril.Formats.Arrow.BinaryView.Batch.Defs
import Silmaril.Proofs.Formats.Arrow.BinaryView.Batch

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView

/-- The parsed count is a bounded nonnegative i64 word and determines the
length of the ordered data descriptor vector. -/
theorem BatchMetadata.count_verified {metadataBytes : KBytes} {maxDataBuffers : Nat}
    (metadata : BatchMetadata metadataBytes maxDataBuffers) :
    metadataBytes.readLE metadata.countOffset 8 = some metadata.dataCount ∧
      metadata.dataCount < 2^63 ∧ metadata.dataCount ≤ maxDataBuffers ∧
      (Batch.descriptors metadata).length = 2 + metadata.dataCount :=
  ⟨metadata.countWord, metadata.signedCount, metadata.countWithin, by
    simp only [Batch.descriptors, List.length_cons, Vector.length_toList]
    change metadata.dataCount + 2 = 2 + metadata.dataCount
    exact Nat.add_comm _ _⟩

namespace Batch

/-- An admitted descriptor selects its exact bounded window in the supplied body. -/
theorem frame_buffer_exact {metadataBytes body : KBytes} {maxDataBuffers : Nat}
    (frame : Frame metadataBytes body maxDataBuffers) {buffer : Buffer}
    (member : buffer ∈ descriptors frame.metadata) :
    (Body.sliceBuffer body buffer).len = buffer.length ∧
      (Body.sliceBuffer body buffer).toList = (body.toList.drop buffer.offset).take buffer.length :=
  Proofs.Formats.Arrow.BinaryView.Batch.frame_buffer_exact frame member

/-- Variadic data retains descriptor order at each physical index. -/
theorem frame_data_at {metadataBytes body : KBytes} {maxDataBuffers : Nat}
    (frame : Frame metadataBytes body maxDataBuffers) (index : Fin frame.metadata.dataCount) :
    frame.buffers.payload.data[index.val]? =
      some (Body.sliceBuffer body frame.metadata.data[index.val]) :=
  Proofs.Formats.Arrow.BinaryView.Batch.frame_data_at frame index

/-- A binary observation composes checked binding with the column wire relation. -/
theorem readBinary_iff (ipc : Arrow.Limits) (limits : Column.Limits)
    (nullable : Bool) (metadataBytes body : KBytes) (values : List (Option KBytes)) :
    readBinary ipc limits nullable metadataBytes body = .ok values ↔
      ∃ frame, bindBuffers ipc limits nullable metadataBytes body = .ok frame ∧
        Column.Wire limits frame.metadata.node nullable frame.buffers values :=
  Proofs.Formats.Arrow.BinaryView.Batch.readBinary_iff ipc limits nullable metadataBytes body values

/-- A text observation decodes the same checked byte windows in order. -/
theorem readUtf8_iff (ipc : Arrow.Limits) (limits : Column.Limits)
    (nullable : Bool) (metadataBytes body : KBytes) (values : List (Option String)) :
    readUtf8 ipc limits nullable metadataBytes body = .ok values ↔
      ∃ frame, bindBuffers ipc limits nullable metadataBytes body = .ok frame ∧
        ∃ slots, Column.Wire limits frame.metadata.node nullable frame.buffers slots ∧
          slots.mapM (·.mapM Column.decodeUtf8) = .ok values :=
  Proofs.Formats.Arrow.BinaryView.Batch.readUtf8_iff ipc limits nullable metadataBytes body values

/-- A successful text read preserves the declared record count and field-node null count. -/
theorem readUtf8_counts {ipc : Arrow.Limits} {limits : Column.Limits}
    {nullable : Bool} {metadataBytes body : KBytes} {values : List (Option String)}
    (read : readUtf8 ipc limits nullable metadataBytes body = .ok values) :
    ∃ frame, bindBuffers ipc limits nullable metadataBytes body = .ok frame ∧
      values.length = frame.metadata.rowCount ∧
      values.countP Option.isNone = frame.metadata.node.nullCount :=
  Proofs.Formats.Arrow.BinaryView.Batch.readUtf8_counts read

end Batch

end Silmaril.Formats.Arrow.BinaryView
