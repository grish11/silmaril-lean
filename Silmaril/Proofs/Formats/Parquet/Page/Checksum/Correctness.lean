module

public import Silmaril.Formats.Parquet.Page.Checksum.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Compression.Checksum.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Page.Checksum

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Page
open Silmaril.Formats.Parquet.Page.Checksum

public theorem signed_bits (signed : Int) : (UInt32.ofInt signed).toNat = (signed % 2 ^ 32).toNat := by
  have nonneg : 0 ≤ signed % (2 ^ 32 : Int) := Int.emod_nonneg _ (by decide)
  have bounded : signed % (2 ^ 32 : Int) < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  have fits : (signed % (2 ^ 32 : Int)).toNat < UInt32.size := by
    change (signed % (2 ^ 32 : Int)).toNat < 4294967296
    omega
  rw [UInt32.ofInt, UInt32.toNat_ofNat', Nat.mod_eq_of_lt fits]

public theorem payload_exact {source : Bytes} {frame : Frame} (extent : PayloadWithin source frame) :
    source.slice? frame.payload.start (some frame.payload.stop) = some (payloadBytes source frame) ∧
    (payloadBytes source frame).length = frame.value.compressedSize := by
  obtain ⟨_, _, width, bound⟩ := extent
  have sliced : source.slice? frame.payload.start (some frame.payload.stop) =
      some (payloadBytes source frame) := by
    apply Bytes.slice?_eq_some_iff.mpr
    refine ⟨by simp [width], bound, Bytes.ext ?_⟩
    rw [Bytes.toList_ofList]
    simp [payloadBytes, Footer.fileBytes, Bytes.toList, ByteArray.data_extract]
  exact ⟨sliced, by simpa [width] using Bytes.length_of_slice? sliced⟩

public theorem verify_absent_iff {maxPayloadBytes : Nat} {source : Bytes} {frame : Frame} :
    verify maxPayloadBytes source frame = .ok .absent ↔
      frame.value.compressedSize ≤ maxPayloadBytes ∧ PayloadWithin source frame ∧
      frame.value.crc = none := by
  by_cases size : frame.value.compressedSize ≤ maxPayloadBytes
  · by_cases extent : PayloadWithin source frame
    · cases field : frame.value.crc with
      | none => simp [verify, Nat.not_lt.mpr size, size, extent, field]
      | some =>
        simp only [verify, ite_eq_right (Nat.not_lt.mpr size), ite_eq_right (not_not_intro extent), field]
        split <;> simp
    · simp [verify, Nat.not_lt.mpr size, extent]
  · simp [verify, Nat.lt_of_not_ge size, size]

public theorem verify_valid_iff {maxPayloadBytes : Nat} {source : Bytes} {frame : Frame}
    {declared : UInt32} :
    verify maxPayloadBytes source frame = .ok (.valid declared) ↔
      frame.value.compressedSize ≤ maxPayloadBytes ∧ PayloadWithin source frame ∧
      frame.value.crc = some declared ∧ Compression.crc32Spec (payloadBytes source frame).toList = declared := by
  by_cases size : frame.value.compressedSize ≤ maxPayloadBytes
  · by_cases extent : PayloadWithin source frame
    · constructor
      · intro verified
        cases field : frame.value.crc with
        | none => simp [verify, Nat.not_lt.mpr size, extent, field] at verified
        | some crc =>
          simp only [verify, ite_eq_right (Nat.not_lt.mpr size), ite_eq_right (not_not_intro extent), field,
            Compression.Checksum.crc32_digest_eq_spec] at verified
          split at verified
          · rename_i matched
            cases verified
            exact ⟨size, extent, rfl, matched⟩
          · simp at verified
      · rintro ⟨_, _, field, matched⟩
        simp [verify, Nat.not_lt.mpr size, extent, field, Compression.Checksum.crc32_digest_eq_spec, matched]
    · simp [verify, Nat.not_lt.mpr size, extent]
  · simp [verify, Nat.lt_of_not_ge size, size]

public theorem verify_mismatch_iff {maxPayloadBytes : Nat} {source : Bytes} {frame : Frame}
    {declared computed : UInt32} :
    verify maxPayloadBytes source frame = .error (.mismatch declared computed) ↔
      frame.value.compressedSize ≤ maxPayloadBytes ∧ PayloadWithin source frame ∧
      frame.value.crc = some declared ∧ Compression.crc32Spec (payloadBytes source frame).toList = computed ∧
      computed ≠ declared := by
  by_cases size : frame.value.compressedSize ≤ maxPayloadBytes
  · by_cases extent : PayloadWithin source frame
    · constructor
      · intro rejected
        cases field : frame.value.crc with
        | none => simp [verify, Nat.not_lt.mpr size, extent, field] at rejected
        | some crc =>
          simp only [verify, ite_eq_right (Nat.not_lt.mpr size), ite_eq_right (not_not_intro extent), field,
            Compression.Checksum.crc32_digest_eq_spec] at rejected
          split at rejected
          · simp at rejected
          · rename_i differs
            cases rejected
            exact ⟨size, extent, rfl, rfl, differs⟩
      · rintro ⟨_, _, field, rfl, differs⟩
        simp [verify, Nat.not_lt.mpr size, extent, field, Compression.Checksum.crc32_digest_eq_spec, differs]
    · simp [verify, Nat.not_lt.mpr size, extent]
  · simp [verify, Nat.lt_of_not_ge size, size]

end Silmaril.Proofs.Formats.Parquet.Page.Checksum
