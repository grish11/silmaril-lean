module

public import Silmaril.Formats.Parquet.Hybrid.Defs
import Silmaril.Proofs.Formats.Parquet.Hybrid.Run
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Hybrid

open Silmaril.Formats Silmaril.Formats.Parquet.Hybrid

private theorem decodeRuns_sound {width fuel remaining : Nat} {input : List UInt8}
    {acc : List (List Nat)} {out : List Nat}
    (h : decodeRuns width fuel remaining input acc = .ok out) :
    ∃ values, Wire width remaining input values ∧ out = acc.reverse.flatten ++ values := by
  induction fuel generalizing remaining input acc out with
  | zero =>
    cases remaining with
    | zero =>
      cases input with
      | nil =>
        cases h
        exact ⟨[], .empty, by simp⟩
      | cons => simp [decodeRuns] at h
    | succ => simp [decodeRuns] at h
  | succ fuel ih =>
    cases remaining with
    | zero =>
      cases input with
      | nil =>
        cases h
        exact ⟨[], .empty, by simp⟩
      | cons => simp [decodeRuns] at h
    | succ remaining =>
      cases hr : readRun width input with
      | error e => simp [decodeRuns, hr] at h
      | ok result =>
        obtain ⟨run, tail⟩ := result
        by_cases fits : run.Fits (remaining + 1)
        · simp only [decodeRuns, hr, ite_eq_left fits] at h
          obtain ⟨values, rest, hout⟩ := ih h
          obtain ⟨valid, bytes⟩ := readRun_ok_iff.mp hr
          refine ⟨_, bytes ▸ Wire.next (by omega) valid fits rest, ?_⟩
          simpa [List.append_assoc] using hout
        · simp [decodeRuns, hr, fits] at h

private theorem decodeRuns_complete {width remaining : Nat} {input : List UInt8}
    {values : List Nat} (wire : Wire width remaining input values)
    {fuel : Nat} (covered : remaining ≤ fuel) (acc : List (List Nat)) :
    decodeRuns width fuel remaining input acc = .ok (acc.reverse.flatten ++ values) := by
  induction wire generalizing fuel acc with
  | empty => cases fuel <;> simp [decodeRuns]
  | @next remaining run tail values positive valid fits rest ih =>
    obtain ⟨rem, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hr : readRun width (run.wire width ++ tail) = .ok (run, tail) :=
        readRun_ok_iff.mpr ⟨valid, rfl⟩
      simp only [decodeRuns, hr, ite_eq_left fits]
      rw [ih (by have := valid.1; omega)]
      simp [List.append_assoc]

private theorem decodeRuns_ok_iff {width expected : Nat} {input : List UInt8} {values : List Nat} :
    decodeRuns width expected expected input [] = .ok values ↔ Wire width expected input values := by
  constructor
  · intro h
    obtain ⟨_, wire, out⟩ := decodeRuns_sound h
    simpa [out] using wire
  · intro h
    simpa using decodeRuns_complete h (Nat.le_refl expected) []

public theorem decode_ok_iff {width expected : Nat} {limits : Limits} {source : Bytes}
    {values : List Nat} :
    decode width expected limits source = .ok values ↔
      width ≤ 32 ∧ expected < runLimit ∧ expected ≤ limits.values ∧
        source.length ≤ limits.bytes ∧ Wire width expected source.toList values := by
  by_cases hw : 32 < width
  · simp [decode, hw, Nat.not_le_of_gt hw]
  · by_cases count : runLimit ≤ expected ∨ limits.values < expected
    · simp only [decode, ite_eq_right hw, ite_eq_left count, reduceCtorEq, false_iff]
      exact fun h => by omega
    · by_cases bytes : limits.bytes < source.length
      · simp [decode, hw, count, bytes, Nat.not_le_of_gt bytes]
      · have hwidth : width ≤ 32 := by omega
        have hcount : expected < runLimit := by omega
        have hlimit : expected ≤ limits.values := by omega
        have hbytes : source.length ≤ limits.bytes := by omega
        simp [decode, hw, count, bytes, hwidth, hcount, hlimit, hbytes, decodeRuns_ok_iff]

private theorem wire_length {width expected : Nat} {input : List UInt8} {values : List Nat}
    (wire : Wire width expected input values) : values.length = expected := by
  induction wire with
  | empty => rfl
  | @next remaining run tail values _ _ _ _ ih =>
    simp only [List.length_append, List.length_take, run_values_length, ih]
    omega

public theorem decode_length {width expected : Nat} {limits : Limits} {source : Bytes}
    {values : List Nat} (h : decode width expected limits source = .ok values) :
    values.length = expected :=
  wire_length (decode_ok_iff.mp h).2.2.2.2

private theorem wire_values_fit {width expected : Nat} {input : List UInt8} {values : List Nat}
    (wire : Wire width expected input values) : ∀ n ∈ values, n < 2 ^ width := by
  induction wire with
  | empty => simp
  | next _ valid _ _ ih =>
    intro n h
    rcases List.mem_append.mp h with hn | hn
    · exact run_values_fit valid n (List.mem_of_mem_take hn)
    · exact ih n hn

public theorem decode_values_fit {width expected : Nat} {limits : Limits} {source : Bytes}
    {values : List Nat} (h : decode width expected limits source = .ok values) :
    ∀ n ∈ values, n < 2 ^ width :=
  wire_values_fit (decode_ok_iff.mp h).2.2.2.2

public theorem decode_encodeRepeated {width count value : Nat} {source : Bytes} {limits : Limits}
    (encoded : encodeRepeated width count value = .ok source)
    (valuesBound : count ≤ limits.values) (bytesBound : source.length ≤ limits.bytes) :
    decode width count limits source = .ok (List.replicate count value) := by
  unfold encodeRepeated at encoded
  split at encoded
  · contradiction
  · rename_i hwidth
    split at encoded
    · contradiction
    · rename_i hcount
      split at encoded
      · contradiction
      · rename_i hvalue
        cases encoded
        apply decode_ok_iff.mpr
        refine ⟨by omega, by omega, valuesBound, bytesBound, ?_⟩
        have valid : (Run.repeated count value).Valid width := ⟨by change 0 < count; omega,
          by change count < runLimit; omega, by change value < 2 ^ width; omega⟩
        have fits : (Run.repeated count value).Fits count := Nat.le_refl count
        have rest : Wire width (count - (Run.repeated count value).size) [] [] := by
          simpa [Run.size] using (Wire.empty (width := width))
        simpa [Run.values, List.take_length] using
          (Wire.next (by omega : 0 < count) valid fits rest)

end Silmaril.Proofs.Formats.Parquet.Hybrid
