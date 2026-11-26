module

public import Silmaril.Formats.Parquet.Page.Checksum.Scan.Defs
import Silmaril.Proofs.Formats.Parquet.Page.Checksum.Scan.Correctness

/-! Verification before decoding and failure context for checked page lists. -/

public section

namespace Silmaril.Formats.Parquet.Page.Checksum

/-- A successful prepass verifies every original frame with its payload cap. -/
theorem verifyFrames_ok {caps : Frame → Nat} {source : Bytes} {frames : List Frame} :
    verifyFrames caps source frames = .ok () ↔
      ∀ frame ∈ frames, ∃ status, verify (caps frame) source frame = .ok status :=
  Proofs.Formats.Parquet.Page.Checksum.Scan.verifyFrames_ok

/-- The error retains the original frame's index, offset, and verifier reason. -/
theorem verifyFrames_errorFrame {caps : Frame → Nat} {source : Bytes} {frames : List Frame}
    {failure : FrameFailure} (failed : verifyFrames caps source frames = .error failure) :
    ∃ frame, frames[failure.index]? = some frame ∧ failure.offset = frame.header.start ∧
      verify (caps frame) source frame = .error failure.reason :=
  Proofs.Formats.Parquet.Page.Checksum.Scan.verifyFrames_errorFrame failed

/-- Both the original parse and every CRC check use the same immutable bytes. -/
theorem readChunkWithCRC_ok {limits : Limits} {caps : Frame → Nat} {source : Bytes}
    {span : Footer.Span} {frames : List Frame}
    (parsed : readChunkWithCRC limits caps source span = .ok frames) :
    readChunk limits source span = .ok frames ∧
      ∀ frame ∈ frames, ∃ status, verify (caps frame) source frame = .ok status :=
  Proofs.Formats.Parquet.Page.Checksum.Scan.readChunkWithCRC_ok parsed

end Silmaril.Formats.Parquet.Page.Checksum
