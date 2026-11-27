module

public import Silmaril.Formats.Arrow.Framing.Defs
import Silmaril.Prelude.Bytes.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow

open Silmaril.Formats.Arrow

theorem readEnvelope_iff (limits : Limits) (input : KBytes) (offset : Nat)
    (envelope : Envelope) (wf : input.wf = true) :
    readEnvelope limits input offset = .ok envelope ↔
      EnvelopeWire limits input.toList offset envelope := by
  have inputLength := KBytes.length_toList input wf
  by_cases aligned : offset % 8 = 0
  · by_cases hasPrefix : offset + 8 ≤ input.len
    · have marker := KBytes.read_eq input offset 4 wf (by omega)
      have size := KBytes.read_eq input (offset + 4) 4 wf (by omega)
      simp only [readEnvelope, readPrefix, EnvelopeWire, ite_eq_right (Nat.not_lt.mpr hasPrefix),
        inputLength, aligned, hasPrefix, true_and, marker, size]
      generalize KBytes.leVal ((input.toList.drop offset).take 4) = m
      generalize KBytes.leVal ((input.toList.drop (offset + 4)).take 4) = n
      by_cases continuation : m = 0xffffffff
      · simp only [continuation, true_and]
        by_cases eos : n = 0
        · cases envelope <;> simp [eos] <;> omega
        · by_cases validSize : n < 2^31 ∧ n % 8 = 0
          · have notBad : ¬ (2^31 ≤ n ∨ n % 8 ≠ 0) := by omega
            by_cases budget : n ≤ limits.metadataBytes
            · by_cases hasMetadata : offset + 8 + n ≤ input.len
              · cases envelope <;>
                  simp [eos, notBad, Nat.not_lt.mpr budget, Nat.not_lt.mpr hasMetadata]
                rintro rfl
                exact ⟨Nat.pos_of_ne_zero eos, validSize.1, validSize.2, budget, hasMetadata⟩
              · have short : input.len < offset + 8 + n := by omega
                cases envelope <;> simp [eos, notBad, Nat.not_lt.mpr budget, short] <;> omega
            · have over : limits.metadataBytes < n := by omega
              cases envelope <;> simp [eos, notBad, over] <;> omega
          · have bad : 2^31 ≤ n ∨ n % 8 ≠ 0 := by omega
            cases envelope <;> simp [eos, bad] <;> omega
      · by_cases legacy : 0 < m ∧ m < 2^31 <;> simp [continuation, legacy]
    · have short : input.len < offset + 8 := by omega
      simp [readEnvelope, EnvelopeWire, aligned, inputLength, hasPrefix, short]
  · simp [readEnvelope, EnvelopeWire, aligned]

theorem metadata_exact {limits : Limits} {input : KBytes} {offset size : Nat}
    (wf : input.wf = true) (read : readEnvelope limits input offset = .ok (.metadata size)) :
    (input.slice (offset + 8) size).toList = (input.toList.drop (offset + 8)).take size := by
  obtain ⟨_, _, _, _, _, _, _, _, bounded⟩ :=
    (readEnvelope_iff limits input offset (.metadata size) wf).mp read
  rw [KBytes.length_toList input wf] at bounded
  exact KBytes.toList_slice input _ _ wf bounded

theorem readBody_iff (limits : Limits) (input : KBytes) (offset size : Nat) (body : KBytes) :
    readBody limits input offset size = .ok body ↔
      offset % 8 = 0 ∧ size % 8 = 0 ∧ size ≤ limits.bodyBytes ∧
        offset + size ≤ input.len ∧ body = input.slice offset size := by
  by_cases aligned : offset % 8 = 0
  · by_cases bodyAligned : size % 8 = 0
    · by_cases budget : size ≤ limits.bodyBytes
      · by_cases available : offset + size ≤ input.len
        · simp [readBody, aligned, bodyAligned, budget, available, Nat.not_lt.mpr, eq_comm]
        · have short : input.len < offset + size := by omega
          simp [readBody, aligned, bodyAligned, budget, Nat.not_lt.mpr, available, short]
      · have over : limits.bodyBytes < size := by omega
        simp [readBody, aligned, bodyAligned, budget, over]
    · simp [readBody, aligned, bodyAligned]
  · simp [readBody, aligned]

theorem body_exact {limits : Limits} {input : KBytes} {offset size : Nat} {body : KBytes}
    (wf : input.wf = true) (read : readBody limits input offset size = .ok body) :
    body.len = size ∧ body.toList = (input.toList.drop offset).take size := by
  obtain ⟨_, _, _, bounded, rfl⟩ := (readBody_iff _ _ _ _ _).mp read
  exact ⟨KBytes.len_slice _ _ _, KBytes.toList_slice _ _ _ wf bounded⟩

end Silmaril.Proofs.Formats.Arrow
