module

public import Silmaril.Formats.Parquet.Page.Checksum.Scan.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.Page.Checksum.Scan

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Page
open Silmaril.Formats.Parquet.Page.Checksum

private theorem go_ok (caps : Frame → Nat) (source : Bytes) (frames : List Frame) (index : Nat) :
    verifyFrames.go caps source index frames = .ok () ↔
      ∀ frame ∈ frames, ∃ status, verify (caps frame) source frame = .ok status := by
  induction frames generalizing index with
  | nil => simp [verifyFrames.go]
  | cons frame rest ih =>
    cases checked : verify (caps frame) source frame with
    | error reason =>
      constructor
      · simp [verifyFrames.go, checked]
      · intro every
        obtain ⟨_, valid⟩ := every frame List.mem_cons_self
        simp [checked] at valid
    | ok status =>
      rw [verifyFrames.go, checked, ih]
      constructor
      · intro later candidate member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact ⟨status, checked⟩
        · exact later candidate inRest
      · intro all candidate member
        exact all candidate (List.mem_cons_of_mem _ member)

theorem verifyFrames_ok {caps : Frame → Nat} {source : Bytes} {frames : List Frame} :
    verifyFrames caps source frames = .ok () ↔
      ∀ frame ∈ frames, ∃ status, verify (caps frame) source frame = .ok status :=
  go_ok caps source frames 0

private theorem go_error {caps : Frame → Nat} {source : Bytes} {failure : FrameFailure}
    (frames : List Frame) (start : Nat)
    (failed : verifyFrames.go caps source start frames = .error failure) :
    ∃ index frame, frames[index]? = some frame ∧ failure.index = start + index ∧
      failure.offset = frame.header.start ∧ verify (caps frame) source frame = .error failure.reason := by
  induction frames generalizing start with
  | nil => cases failed
  | cons frame rest ih =>
    cases checked : verify (caps frame) source frame with
    | error reason =>
      rw [verifyFrames.go, checked] at failed
      cases failed
      exact ⟨0, frame, rfl, by simp, rfl, checked⟩
    | ok status =>
      rw [verifyFrames.go, checked] at failed
      obtain ⟨index, later, found, ordinal, offset, reason⟩ := ih (start + 1) failed
      exact ⟨index + 1, later, by simpa using found, by omega, offset, reason⟩

theorem verifyFrames_errorFrame {caps : Frame → Nat} {source : Bytes} {frames : List Frame}
    {failure : FrameFailure} (failed : verifyFrames caps source frames = .error failure) :
    ∃ frame, frames[failure.index]? = some frame ∧ failure.offset = frame.header.start ∧
      verify (caps frame) source frame = .error failure.reason := by
  obtain ⟨index, frame, found, position, offset, reason⟩ := go_error frames 0 failed
  exact ⟨frame, by simpa [position] using found, offset, reason⟩

theorem readChunkWithCRC_ok {limits : Limits} {caps : Frame → Nat} {source : Bytes}
    {span : Footer.Span} {frames : List Frame}
    (parsed : readChunkWithCRC limits caps source span = .ok frames) :
    readChunk limits source span = .ok frames ∧
      ∀ frame ∈ frames, ∃ status, verify (caps frame) source frame = .ok status := by
  cases read : readChunk limits source span with
  | error reason => simp [readChunkWithCRC, read, Except.mapError, Bind.bind, Except.bind] at parsed
  | ok found =>
    cases checked : verifyFrames caps source found with
    | error reason => simp [readChunkWithCRC, read, checked, Except.mapError, Bind.bind, Except.bind] at parsed
    | ok status =>
      cases status
      have eq : found = frames := by
        simpa [readChunkWithCRC, read, checked, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure] using parsed
      subst frames
      exact ⟨rfl, verifyFrames_ok.mp checked⟩

end Silmaril.Proofs.Formats.Parquet.Page.Checksum.Scan
