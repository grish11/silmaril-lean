module

public import Silmaril.Formats.Parquet.Hybrid.Defs
import Silmaril.Proofs.Formats.Parquet.Hybrid.Header
import Silmaril.Prelude.Bytes.Digits.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Hybrid

open Silmaril.Formats.Parquet.Hybrid

private theorem repeatedCapacity (width : Nat) : 2 ^ width ≤ 256 ^ repeatedByteCount width := by
  rw [show 256 = 2 ^ 8 by decide, ← Nat.pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  unfold repeatedByteCount
  omega

private theorem readRun_sound {width : Nat} {input tail : List UInt8} {run : Run}
    (h : readRun width input = .ok (run, tail)) :
    run.Valid width ∧ input = run.wire width ++ tail := by
  cases hh : readHeader input with
  | error e => simp [readRun, hh] at h
  | ok result =>
    obtain ⟨code, bytes⟩ := result
    obtain ⟨bound, octets⟩ := readHeader_ok_iff.mp hh
    by_cases zero : code / 2 = 0
    · simp [readRun, hh, zero] at h
    · by_cases repeated : code % 2 = 0
      · cases hp : takeExact (repeatedByteCount width) bytes with
        | error e => simp [readRun, hh, zero, repeated, hp] at h
        | ok result =>
          obtain ⟨payload, rest⟩ := result
          by_cases fits : KBytes.leVal payload < 2 ^ width
          · simp [readRun, hh, zero, repeated, hp, fits] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨sized, body⟩ := takeExact_ok_iff.mp hp
            refine ⟨⟨by change 0 < code / 2; omega, by change code / 2 < runLimit; omega, fits⟩, ?_⟩
            have tag : code / 2 * 2 = code := by omega
            simp only [Run.wire, tag, ← sized, KBytes.unpack_leVal, List.append_assoc, ← body, octets]
          · simp [readRun, hh, zero, repeated, hp, fits] at h
      · by_cases cap : code / 2 * 8 < runLimit
        · cases hp : takeExact (code / 2 * width) bytes with
          | error e => simp [readRun, hh, zero, repeated, cap, hp] at h
          | ok result =>
            obtain ⟨payload, rest⟩ := result
            simp [readRun, hh, zero, repeated, cap, hp] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨sized, body⟩ := takeExact_ok_iff.mp hp
            refine ⟨⟨by change 0 < code / 2 * 8; omega, cap, sized⟩, ?_⟩
            have tag : code / 2 * 2 + 1 = code := by omega
            simp only [Run.wire, tag, List.append_assoc, ← body, octets]
        · simp [readRun, hh, zero, repeated, cap] at h

private theorem readRun_complete {width : Nat} {run : Run} (valid : run.Valid width)
    (rest : List UInt8) : readRun width (run.wire width ++ rest) = .ok (run, rest) := by
  cases run with
  | repeated count value =>
    obtain ⟨positive, bound, fits⟩ := valid
    change 0 < count at positive
    change count < runLimit at bound
    change value < 2 ^ width at fits
    let payload := KBytes.unpack (repeatedByteCount width) value
    have hh : readHeader (uleb (count * 2) ++ (payload ++ rest)) =
        .ok (count * 2, payload ++ rest) := readHeader_ok_iff.mpr ⟨by omega, rfl⟩
    have hp : takeExact (repeatedByteCount width) (payload ++ rest) =
        .ok (payload, rest) := takeExact_ok_iff.mpr ⟨KBytes.length_unpack _ _, rfl⟩
    have hv : KBytes.leVal payload = value := by
      exact (KBytes.leVal_unpack _ _).trans
        (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le fits (repeatedCapacity width)))
    have units : count * 2 / 2 = count := by omega
    have tag : count * 2 % 2 = 0 := by omega
    change readRun width ((uleb (count * 2) ++ payload) ++ rest) = _
    rw [List.append_assoc]
    simp only [readRun, hh, units, ite_eq_right (Nat.ne_of_gt positive), ite_eq_left tag, hp,
      hv, ite_eq_left fits]
  | packed groups payload =>
    obtain ⟨positive, bound, sized⟩ := valid
    change 0 < groups * 8 at positive
    change groups * 8 < runLimit at bound
    change payload.length = groups * width at sized
    have hh : readHeader (uleb (groups * 2 + 1) ++ (payload ++ rest)) =
        .ok (groups * 2 + 1, payload ++ rest) := readHeader_ok_iff.mpr ⟨by omega, rfl⟩
    have hp : takeExact (groups * width) (payload ++ rest) = .ok (payload, rest) :=
      takeExact_ok_iff.mpr ⟨sized, rfl⟩
    have units : (groups * 2 + 1) / 2 = groups := by omega
    have tag : ¬ (groups * 2 + 1) % 2 = 0 := by omega
    have nonzero : groups ≠ 0 := by omega
    change readRun width ((uleb (groups * 2 + 1) ++ payload) ++ rest) = _
    rw [List.append_assoc]
    simp only [readRun, hh, units, ite_eq_right nonzero, ite_eq_right tag, ite_eq_left bound, hp]

public theorem readRun_ok_iff {width : Nat} {input rest : List UInt8} {run : Run} :
    readRun width input = .ok (run, rest) ↔ run.Valid width ∧ input = run.wire width ++ rest := by
  exact ⟨readRun_sound, fun ⟨valid, wire⟩ => wire ▸ readRun_complete valid rest⟩

public theorem unpackGroup_getElem (width : Nat) (bytes : List UInt8) {i : Nat}
    (hi : i < (unpackGroup width bytes).length) :
    (unpackGroup width bytes)[i] = KBytes.leVal bytes / (2 ^ width) ^ i % (2 ^ width) := by
  exact List.getElem_ofFn (f := fun bit : Fin 8 =>
    KBytes.leVal bytes / (2 ^ width) ^ bit.val % (2 ^ width)) hi

private theorem unpackGroups_fit (width groups : Nat) (bytes : List UInt8) (acc : List Nat)
    (bounded : ∀ n ∈ acc, n < 2 ^ width) :
    ∀ n ∈ unpackGroups width groups bytes acc, n < 2 ^ width := by
  induction groups generalizing bytes acc with
  | zero => simpa [unpackGroups] using bounded
  | succ groups ih =>
    rw [unpackGroups]
    apply ih
    intro n h
    rcases List.mem_append.mp h with hn | hn
    · have hm := List.mem_reverse.mp hn
      unfold unpackGroup at hm
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
      exact Nat.mod_lt _ (Nat.pow_pos (by decide))
    · exact bounded n hn

public theorem run_values_fit {width : Nat} {run : Run} (valid : run.Valid width) :
    ∀ n ∈ run.values width, n < 2 ^ width := by
  cases run with
  | repeated count value =>
    intro n h
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp h
    exact valid.2.2
  | packed groups payload =>
    exact unpackGroups_fit width groups payload [] (by simp)

private theorem unpackGroups_length (width groups : Nat) (bytes : List UInt8) (acc : List Nat) :
    (unpackGroups width groups bytes acc).length = acc.length + groups * 8 := by
  induction groups generalizing bytes acc with
  | zero => simp [unpackGroups]
  | succ groups ih =>
    rw [unpackGroups, ih]
    simp only [List.length_append, List.length_reverse, unpackGroup, List.length_ofFn]
    omega

public theorem run_values_length (width : Nat) (run : Run) :
    (run.values width).length = run.size := by
  cases run with
  | repeated count value => simp [Run.values, Run.size]
  | packed groups payload => simp [Run.values, Run.size, unpackGroups_length]

end Silmaril.Proofs.Formats.Parquet.Hybrid
