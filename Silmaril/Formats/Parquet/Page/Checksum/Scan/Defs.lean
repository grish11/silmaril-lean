module

public import Silmaril.Formats.Parquet.Page.Checksum.Defs

/-! Check a column's original framed pages before decoding any body. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Page.Checksum

structure FrameFailure where
  index : Nat
  offset : Nat
  reason : Error
  deriving DecidableEq, Repr

/-- Verify every original frame in order. An absent checksum is allowed.
The index includes a leading dictionary frame when present. -/
def verifyFrames (maxPayloadBytes : Frame → Nat) (source : Bytes) (frames : List Frame) :
    Except FrameFailure Unit := go 0 frames
where
  go (index : Nat) : List Frame → Except FrameFailure Unit
    | [] => .ok ()
    | frame :: rest =>
      match verify (maxPayloadBytes frame) source frame with
      | .ok _ => go (index + 1) rest
      | .error reason => .error ⟨index, frame.header.start, reason⟩

inductive ReadError where
  | page (reason : Page.Error)
  | checksum (reason : FrameFailure)
  deriving DecidableEq, Repr

/-- Check and return the exact frame list parsed from the original snapshot. -/
def readChunkWithCRC (limits : Page.Limits) (maxPayloadBytes : Frame → Nat) (source : Bytes)
    (span : Footer.Span) : Except ReadError (List Frame) := do
  let frames ← (Page.readChunk limits source span).mapError .page
  (verifyFrames maxPayloadBytes source frames).mapError .checksum
  pure frames

end Silmaril.Formats.Parquet.Page.Checksum
