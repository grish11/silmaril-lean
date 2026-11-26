module

public import Silmaril.Formats.Arrow.BinaryView.Batch.Defs
import Silmaril.Formats.Arrow.BinaryView.Column.Thms
import Silmaril.Formats.Arrow.Layout.Thms
import Silmaril.Prelude.Bytes.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView.Batch

open Silmaril.Formats
open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.BinaryView.Batch

theorem frame_buffer_exact {metadataBytes body : KBytes} {maxDataBuffers : Nat}
    (frame : Frame metadataBytes body maxDataBuffers) {buffer : Buffer}
    (member : buffer ∈ descriptors frame.metadata) :
    (Body.sliceBuffer body buffer).len = buffer.length ∧
      (Body.sliceBuffer body buffer).toList = (body.toList.drop buffer.offset).take buffer.length := by
  have fits := frame.layout.mem_fits member
  exact ⟨KBytes.len_slice _ _ _, KBytes.toList_slice _ _ _ frame.source fits.2.2⟩

theorem frame_data_at {metadataBytes body : KBytes} {maxDataBuffers : Nat}
    (frame : Frame metadataBytes body maxDataBuffers) (index : Fin frame.metadata.dataCount) :
    frame.buffers.payload.data[index.val]? =
      some (Body.sliceBuffer body frame.metadata.data[index.val]) := by
  simp [Frame.buffers, index.isLt]

private theorem mapError_ok_iff {ε κ α : Type} (f : ε → κ) (result : Except ε α) (value : α) :
    result.mapError f = .ok value ↔ result = .ok value := by
  cases result <;> simp [Except.mapError]

theorem readBinary_iff (ipc : Arrow.Limits) (limits : BinaryView.Column.Limits)
    (nullable : Bool) (metadataBytes body : KBytes) (values : List (Option KBytes)) :
    readBinary ipc limits nullable metadataBytes body = .ok values ↔
      ∃ frame, bindBuffers ipc limits nullable metadataBytes body = .ok frame ∧
        BinaryView.Column.Wire limits frame.metadata.node nullable frame.buffers values := by
  cases bound : bindBuffers ipc limits nullable metadataBytes body with
  | error cause => simp [readBinary, bound, bind, Except.bind]
  | ok frame =>
    simp [readBinary, bound, bind, Except.bind, mapError_ok_iff, BinaryView.Column.readBinary_iff]

theorem readUtf8_iff (ipc : Arrow.Limits) (limits : BinaryView.Column.Limits)
    (nullable : Bool) (metadataBytes body : KBytes) (values : List (Option String)) :
    readUtf8 ipc limits nullable metadataBytes body = .ok values ↔
      ∃ frame, bindBuffers ipc limits nullable metadataBytes body = .ok frame ∧
        ∃ slots, BinaryView.Column.Wire limits frame.metadata.node nullable frame.buffers slots ∧
          slots.mapM (·.mapM BinaryView.Column.decodeUtf8) = .ok values := by
  cases bound : bindBuffers ipc limits nullable metadataBytes body with
  | error cause => simp [readUtf8, bound, bind, Except.bind]
  | ok frame =>
    simp [readUtf8, bound, bind, Except.bind, mapError_ok_iff, BinaryView.Column.readUtf8_iff]

theorem readUtf8_counts {ipc : Arrow.Limits} {limits : BinaryView.Column.Limits}
    {nullable : Bool} {metadataBytes body : KBytes} {values : List (Option String)}
    (read : readUtf8 ipc limits nullable metadataBytes body = .ok values) :
    ∃ frame, bindBuffers ipc limits nullable metadataBytes body = .ok frame ∧
      values.length = frame.metadata.rowCount ∧
      values.countP Option.isNone = frame.metadata.node.nullCount := by
  obtain ⟨frame, bound, slots, wire, decoded⟩ := (readUtf8_iff _ _ _ _ _ _).1 read
  have column := (BinaryView.Column.readUtf8_iff _ _ _ _ _).2 ⟨slots, wire, decoded⟩
  obtain ⟨count, nulls⟩ := BinaryView.Column.readUtf8_counts column
  exact ⟨frame, bound, count.trans frame.rows, nulls⟩

end Silmaril.Proofs.Formats.Arrow.BinaryView.Batch
