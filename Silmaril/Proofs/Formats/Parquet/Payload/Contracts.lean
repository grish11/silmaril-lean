module

public import Silmaril.Formats.Parquet.Payload.Defs
import Silmaril.Formats.Compression.Snappy.Thms
import Silmaril.Formats.Compression.Lz4Raw.Thms
import Silmaril.Formats.Compression.Inflate.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Payload

open Silmaril.Formats.Parquet.Payload
open Silmaril.Formats.Parquet.Payload.Internal
open Silmaril.Formats.Compression
open Inflate.Stream

theorem hasLength_iff {n : Nat} {input : List UInt8} :
    hasLength n input = true ↔ input.length = n := by
  induction n generalizing input with
  | zero => cases input <;> simp [hasLength]
  | succ n ih => cases input <;> simp [hasLength, ih]

/-- This is an invariant for any number of calls, including schedules
    interrupted by an error or an unfinished member. -/
theorem driveGzip_output_le (expected fuel : Nat) (machine : MemberMachine)
    (fits : machine.output.length ≤ expected) :
    (driveGzip expected fuel machine).output.length ≤ expected := by
  induction fuel generalizing machine with
  | zero => exact fits
  | succ fuel ih =>
    unfold driveGzip
    split
    · apply ih
      obtain ⟨emitted, output, room⟩ := Inflate.member_call_output .v131 machine (gzipCall expected machine)
      rw [output, List.length_append]
      change emitted.length ≤ expected - machine.output.length at room
      omega
    · exact fits

private theorem driveGzip_trace (expected fuel : Nat) (machine : MemberMachine) :
    ∃ calls, RawRuns.deliveredInput calls = [] ∧
      MemberMachine.runCalls .v131 machine calls = driveGzip expected fuel machine := by
  induction fuel generalizing machine with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ fuel ih =>
    unfold driveGzip
    split
    · obtain ⟨calls, empty, run⟩ := ih (machine.applyCall .v131 (gzipCall expected machine))
      refine ⟨gzipCall expected machine :: calls, ?_, run⟩
      simpa [RawRuns.deliveredInput, gzipCall] using empty
    · exact ⟨[], rfl, rfl⟩

private theorem noUnreadBytes {reservoir : Reservoir} {reader : LSBReader}
    (normalized : reservoir.Normalizes reader) (empty : reservoir.bits = 0 ∧ reservoir.input = []) :
    reader.input = [] := by
  have count : reader.count = 0 := by simpa [empty.1] using normalized.2.1
  have bits := normalized.2.2.1.2
  have exhausted : bytesBits reader.input = [] := by
    simpa [Reservoir.unread, empty.1, empty.2, count, natBits, bytesBits] using bits
  cases input : reader.input with
  | nil => rfl
  | cons byte rest => simp [input, bytesBits, natBits] at exhausted

private theorem driveGzip_done {bounds : Bounds} {input : List UInt8} {state : RawState}
    (finished : driveGzip bounds.expectedSize bounds.gzipCallLimit (MemberMachine.start .gzip input) =
      .done state)
    (empty : state.reservoir.bits = 0 ∧ state.reservoir.input = []) :
    Gzip.decoder input = some (state.output, []) := by
  obtain ⟨calls, unwritten, execution⟩ :=
    driveGzip_trace bounds.expectedSize bounds.gzipCallLimit (MemberMachine.start .gzip input)
  obtain ⟨reader, normalized, meaning⟩ := Inflate.member_calls_invariant .v131 .gzip input calls
  rw [execution, finished] at normalized meaning
  have unused : reader.input = [] := noUnreadBytes normalized empty
  simpa [Inflate.shared_gzip, unwritten, MemberMachine.denote, MemberSemantics.inputView,
    Reservoir.readerFeed, unused] using meaning []

private theorem decodeGzip_sound {bounds : Bounds} {input out : List UInt8}
    (h : decodeGzip bounds input = .ok out) : Gzip.decoder input = some (out, []) := by
  unfold decodeGzip at h
  dsimp only at h
  split at h
  · cases h
  · next state finished =>
    split at h
    · next empty =>
      cases h
      exact driveGzip_done finished empty
    · cases h
  · split at h <;> cases h

private theorem decodeCodec_sound {bounds : Bounds} {codec : Silmaril.Formats.Parquet.Payload.Codec} {input out : List UInt8}
    (h : decodeCodec bounds input codec = .ok out) : Decodes bounds.expectedSize codec input out := by
  cases codec with
  | uncompressed => cases h; exact .uncompressed input
  | gzip => exact .gzip (decodeGzip_sound h)
  | snappy =>
    cases decoded : Snappy.decode bounds.expectedSize input with
    | error error =>
      cases error with
      | malformed reason => cases reason <;> simp [decodeCodec, decoded] at h
      | unsupported feature => simp [decodeCodec, decoded] at h
      | limited declared limit => simp [decodeCodec, decoded] at h
    | ok bytes =>
      simp [decodeCodec, decoded] at h
      subst out
      obtain ⟨_, parsed, meaning, _, _⟩ := Snappy.decode_sound decoded
      exact .snappy parsed meaning
  | lz4Raw =>
    cases decoded : Lz4Raw.decode
        ⟨bounds.compressedSize, bounds.compressedLimit, bounds.expectedSize, bounds.outputLimit⟩ input with
    | error error => cases error <;> simp [decodeCodec, decoded] at h
    | ok bytes =>
      simp [decodeCodec, decoded] at h
      subst out
      obtain ⟨_, parsed, meaning, _, _, _, _⟩ := Lz4Raw.decode_sound decoded
      exact .lz4Raw parsed meaning
  | lzo | brotli | lz4 | zstd => cases h

theorem decode_sound {bounds : Bounds} {codecId : Int} {input out : List UInt8}
    (h : decode bounds codecId input = .ok out) :
    ∃ codec, Codec.ofId codecId = some codec ∧ Decodes bounds.expectedSize codec input out ∧
      input.length = bounds.compressedSize ∧ input.length ≤ bounds.compressedLimit ∧
      out.length = bounds.expectedSize ∧ out.length ≤ bounds.outputLimit := by
  unfold decode at h
  split at h
  · cases h
  · rename_i compressedFits
    split at h
    · cases h
    · rename_i outputFits
      split at h
      · cases h
      · rename_i extent
        have inputSize : input.length = bounds.compressedSize :=
          hasLength_iff.mp (by simpa using extent)
        cases tag : Codec.ofId codecId with
        | none => simp [tag] at h
        | some codec =>
          cases decompressed : decodeCodec bounds input codec with
          | error error => simp [tag, decompressed, bind, Except.bind] at h
          | ok bytes =>
            simp only [tag, decompressed, bind, Except.bind] at h
            split at h
            · next exactSize =>
              cases h
              exact ⟨codec, rfl, decodeCodec_sound decompressed, inputSize, by omega,
                exactSize, by omega⟩
            · cases h

theorem decode_rejects {bounds : Bounds} {codecId : Int} {input : List UInt8}
    (h : ∀ codec out, Codec.ofId codecId = some codec → out.length = bounds.expectedSize →
      ¬ Decodes bounds.expectedSize codec input out) :
    ∃ error, decode bounds codecId input = .error error := by
  cases result : decode bounds codecId input with
  | error error => exact ⟨error, rfl⟩
  | ok out =>
    obtain ⟨codec, tag, meaning, _, _, size, _⟩ := decode_sound result
    exact False.elim (h codec out tag size meaning)

theorem decode_gzip_no_exact_member {bounds : Bounds} {input : List UInt8}
    (h : ∀ out, Gzip.decoder input ≠ some (out, [])) :
    ∃ error, decode bounds 2 input = .error error := by
  apply decode_rejects
  intro codec out tag _ meaning
  change some Silmaril.Formats.Parquet.Payload.Codec.gzip = some codec at tag
  cases tag
  cases meaning with
  | gzip exactMember => exact h out exactMember

theorem decode_bad_extent {bounds : Bounds} {codecId : Int} {input : List UInt8}
    (compressed : bounds.compressedSize ≤ bounds.compressedLimit)
    (output : bounds.expectedSize ≤ bounds.outputLimit)
    (extent : input.length ≠ bounds.compressedSize) :
    decode bounds codecId input = .error .compressedSizeMismatch := by
  simp [decode, Nat.not_lt.mpr compressed, Nat.not_lt.mpr output, hasLength_iff, extent]

end Silmaril.Proofs.Formats.Parquet.Payload
