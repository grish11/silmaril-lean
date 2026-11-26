module

public import Silmaril.Formats.Parquet.Page.Checksum.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Proofs.Formats.Parquet.Page.Checksum.Correctness

/-! Exact body extent and agreement with the IEEE CRC-32 model. -/

public section

namespace Silmaril.Formats.Parquet.Page.Checksum

/-- The signed Thrift field and its unsigned CRC carry the same 32 bits. -/
theorem signed_bits (signed : Int) : (UInt32.ofInt signed).toNat = (signed % 2 ^ 32).toNat :=
  Proofs.Formats.Parquet.Page.Checksum.signed_bits signed

/-- The existing framing witness supplies the verifier's geometry and bound. -/
theorem payloadWithin_of_frameWithin {source : Bytes} {chunk : Footer.Span}
    {cursor : Nat} {frame : Frame} (within : FrameWithin chunk cursor frame)
    (bound : chunk.stop ≤ source.length) : PayloadWithin source frame := by
  exact ⟨within.headerStart ▸ within.headerProgress, within.adjacent, within.payloadWidth,
    Nat.le_trans within.chunkStop bound⟩

theorem payloadWithin_of_readPage {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {cursor : Nat} {frame : Frame} (parsed : readPage limits source chunk cursor = .ok frame) :
    PayloadWithin source frame :=
  let ⟨within, bound⟩ := readPage_within parsed
  payloadWithin_of_frameWithin within bound

/-- The checked body is the exact source slice with the advertised on-disk length. -/
theorem payload_exact {source : Bytes} {frame : Frame} (extent : PayloadWithin source frame) :
    source.slice? frame.payload.start (some frame.payload.stop) = some (payloadBytes source frame) ∧
    (payloadBytes source frame).length = frame.value.compressedSize :=
  Proofs.Formats.Parquet.Page.Checksum.payload_exact extent

theorem verify_absent_iff {maxPayloadBytes : Nat} {source : Bytes} {frame : Frame} :
    verify maxPayloadBytes source frame = .ok .absent ↔
      frame.value.compressedSize ≤ maxPayloadBytes ∧ PayloadWithin source frame ∧
      frame.value.crc = none :=
  Proofs.Formats.Parquet.Page.Checksum.verify_absent_iff

theorem verify_valid_iff {maxPayloadBytes : Nat} {source : Bytes} {frame : Frame}
    {declared : UInt32} :
    verify maxPayloadBytes source frame = .ok (.valid declared) ↔
      frame.value.compressedSize ≤ maxPayloadBytes ∧ PayloadWithin source frame ∧
      frame.value.crc = some declared ∧
      Compression.crc32Spec (payloadBytes source frame).toList = declared :=
  Proofs.Formats.Parquet.Page.Checksum.verify_valid_iff

theorem verify_mismatch_iff {maxPayloadBytes : Nat} {source : Bytes} {frame : Frame}
    {declared computed : UInt32} :
    verify maxPayloadBytes source frame = .error (.mismatch declared computed) ↔
      frame.value.compressedSize ≤ maxPayloadBytes ∧ PayloadWithin source frame ∧
      frame.value.crc = some declared ∧
      Compression.crc32Spec (payloadBytes source frame).toList = computed ∧
      computed ≠ declared :=
  Proofs.Formats.Parquet.Page.Checksum.verify_mismatch_iff

end Silmaril.Formats.Parquet.Page.Checksum
