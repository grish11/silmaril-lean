module

public import Silmaril.Formats.Parquet.Hybrid.Defs
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Hybrid

open Silmaril.Formats.Parquet.Hybrid

private theorem readULEB_sound {fuel value : Nat} {input rest : List UInt8}
    (h : readULEB fuel input = .ok (value, rest)) : input = uleb value ++ rest := by
  induction fuel generalizing input value rest with
  | zero => simp [readULEB] at h
  | succ fuel ih =>
    cases input with
    | nil => simp [readULEB] at h
    | cons byte bytes =>
      by_cases terminal : byte.toNat < 128
      · simp [readULEB, terminal] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [uleb, ite_eq_left terminal]
        simp
      · cases hr : readULEB fuel bytes with
        | error e => simp [readULEB, terminal, hr] at h
        | ok result =>
          obtain ⟨high, tail⟩ := result
          by_cases hz : high = 0
          · simp [readULEB, terminal, hr, hz] at h
          · simp [readULEB, terminal, hr, hz] at h
            obtain ⟨rfl, rfl⟩ := h
            have hb := byte.toNat_lt
            have nonterminal : ¬ byte.toNat - 128 + 128 * high < 128 := by omega
            rw [uleb, ite_eq_right nonterminal, List.cons_append]
            have hlo : 128 + (byte.toNat - 128 + 128 * high) % 128 = byte.toNat := by omega
            have hhi : (byte.toNat - 128 + 128 * high) / 128 = high := by omega
            rw [hlo, hhi, UInt8.ofNat_toNat, ih hr]

private theorem readULEB_complete {fuel value : Nat} (positive : 0 < fuel)
    (bound : value < 128 ^ fuel) (rest : List UInt8) :
    readULEB fuel (uleb value ++ rest) = .ok (value, rest) := by
  induction fuel generalizing value with
  | zero => omega
  | succ fuel ih =>
    rw [uleb]
    by_cases terminal : value < 128
    · have byte : (UInt8.ofNat value).toNat = value := by
        change value % 256 = value
        exact Nat.mod_eq_of_lt (by omega)
      simp [terminal, readULEB, byte]
    · have highBound : value / 128 < 128 ^ fuel :=
        (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [Nat.pow_succ] using bound)
      have nonzero : value / 128 ≠ 0 := by omega
      have fuelPositive : 0 < fuel := by
        cases fuel with
        | zero => simp at highBound; omega
        | succ _ => omega
      have byte : (UInt8.ofNat (128 + value % 128)).toNat = 128 + value % 128 := by
        change (128 + value % 128) % 256 = _
        exact Nat.mod_eq_of_lt (by omega)
      simp only [ite_eq_right terminal, List.cons_append, readULEB, byte,
        show ¬ 128 + value % 128 < 128 by omega, ite_false,
        ih fuelPositive highBound, ite_eq_right nonzero]
      congr 2
      omega

public theorem readHeader_ok_iff {input rest : List UInt8} {code : Nat} :
    readHeader input = .ok (code, rest) ↔ code < 2 * runLimit ∧ input = uleb code ++ rest := by
  constructor
  · intro h
    cases hr : readULEB 5 input with
    | error e => simp [readHeader, hr] at h
    | ok result =>
      obtain ⟨value, tail⟩ := result
      by_cases bound : value < 2 * runLimit
      · simp [readHeader, hr, bound] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨bound, readULEB_sound hr⟩
      · simp [readHeader, hr, bound] at h
  · rintro ⟨bound, rfl⟩
    have capacity : 2 * runLimit ≤ 128 ^ 5 := by decide
    have header := readULEB_complete (fuel := 5) (by decide) (Nat.lt_of_lt_of_le bound capacity) rest
    simp [readHeader, header, bound]

public theorem takeExact_ok_iff {size : Nat} {input payload rest : List UInt8} :
    takeExact size input = .ok (payload, rest) ↔
      payload.length = size ∧ input = payload ++ rest := by
  constructor
  · intro h
    simp only [takeExact] at h
    split at h
    · rename_i sized
      cases h
      exact ⟨sized, (List.take_append_drop size input).symm⟩
    · contradiction
  · rintro ⟨sized, rfl⟩
    simp [takeExact, List.take_left' sized, List.drop_left' sized, sized]

end Silmaril.Proofs.Formats.Parquet.Hybrid
