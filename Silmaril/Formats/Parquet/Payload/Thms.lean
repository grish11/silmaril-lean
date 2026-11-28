module

public import Silmaril.Formats.Parquet.Payload.Defs
import Silmaril.Proofs.Formats.Parquet.Payload.Contracts

/-! # Bounds, dispatch and exactness of Parquet payload decoding -/

public section

namespace Silmaril.Formats.Parquet.Payload

open Silmaril.Formats.Compression.Inflate.Stream (MemberMachine)

/-- All known Parquet codec IDs are recovered, including unsupported codecs. -/
theorem Codec.ofId_id (codec : Codec) : ofId codec.id = some codec := by cases codec <;> rfl

/-- Every prefix of the GZIP schedule respects the output cap, including
    runs without a successful member or trailer. -/
theorem driveGzip_output_le (expected fuel : Nat) (machine : MemberMachine)
    (fits : machine.output.length ≤ expected) :
    (Internal.driveGzip expected fuel machine).output.length ≤ expected :=
  Proofs.Formats.Parquet.Payload.driveGzip_output_le expected fuel machine fits

/-- The bounded extent test succeeds exactly at the declared input length. -/
theorem hasLength_iff {n : Nat} {input : List UInt8} :
    Internal.hasLength n input = true ↔ input.length = n :=
  Proofs.Formats.Parquet.Payload.hasLength_iff

/-- Success uses the selected codec's exact payload relation, with both
    supplied sizes and bounds. -/
theorem decode_sound {bounds : Bounds} {codecId : Int} {input out : List UInt8}
    (h : decode bounds codecId input = .ok out) :
    ∃ codec, Codec.ofId codecId = some codec ∧ Decodes bounds.expectedSize codec input out ∧
      input.length = bounds.compressedSize ∧ input.length ≤ bounds.compressedLimit ∧
      out.length = bounds.expectedSize ∧ out.length ≤ bounds.outputLimit :=
  Proofs.Formats.Parquet.Payload.decode_sound h

/-- A result requires the selected codec’s denotation at the expected length. -/
theorem decode_rejects {bounds : Bounds} {codecId : Int} {input : List UInt8}
    (h : ∀ codec out, Codec.ofId codecId = some codec → out.length = bounds.expectedSize →
      ¬ Decodes bounds.expectedSize codec input out) :
    ∃ error, decode bounds codecId input = .error error :=
  Proofs.Formats.Parquet.Payload.decode_rejects h

/-- A malformed member or a proper GZIP member followed by a suffix cannot
    succeed as a single-member payload. -/
theorem decode_gzip_no_exact_member {bounds : Bounds} {input : List UInt8}
    (h : ∀ out, Compression.Gzip.decoder input ≠ some (out, [])) :
    ∃ error, decode bounds 2 input = .error error :=
  Proofs.Formats.Parquet.Payload.decode_gzip_no_exact_member h

theorem decode_compressed_limit {bounds : Bounds} {codecId : Int} {input : List UInt8}
    (h : bounds.compressedLimit < bounds.compressedSize) :
    decode bounds codecId input = .error .compressedLimit := by
  simp [decode, h]

theorem decode_output_limit {bounds : Bounds} {codecId : Int} {input : List UInt8}
    (compressed : bounds.compressedSize ≤ bounds.compressedLimit)
    (output : bounds.outputLimit < bounds.expectedSize) :
    decode bounds codecId input = .error .outputLimit := by
  simp [decode, Nat.not_lt.mpr compressed, output]

theorem decode_bad_extent {bounds : Bounds} {codecId : Int} {input : List UInt8}
    (compressed : bounds.compressedSize ≤ bounds.compressedLimit)
    (output : bounds.expectedSize ≤ bounds.outputLimit)
    (extent : input.length ≠ bounds.compressedSize) :
    decode bounds codecId input = .error .compressedSizeMismatch :=
  Proofs.Formats.Parquet.Payload.decode_bad_extent compressed output extent

end Silmaril.Formats.Parquet.Payload
