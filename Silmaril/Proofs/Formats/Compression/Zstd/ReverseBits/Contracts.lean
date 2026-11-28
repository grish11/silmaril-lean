module

public import Silmaril.Formats.Compression.Zstd.ReverseBits.Defs

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.ReverseBits

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Zstd.ReverseBits
open Silmaril.Formats.Compression.Zstd.ReverseBits.Internal

private theorem msbBits_length (word width : Nat) : (msbBits word width).length = width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [msbBits, ih]

private theorem prior_length (prior : List UInt8) :
    (prior.flatMap (fun byte => msbBits byte.toNat 8)).length = 8 * prior.length := by
  induction prior with
  | nil => rfl
  | cons byte prior ih =>
    simp only [List.flatMap_cons, List.length_append, msbBits_length, ih, List.length_cons]
    omega

theorem bits_length (cursor : Cursor) : cursor.bits.length = cursor.remaining := by
  simp only [Cursor.bits, Cursor.remaining, List.length_append, msbBits_length, prior_length]

theorem isEmpty_iff (cursor : Cursor) : cursor.isEmpty = true ↔ cursor.bits = [] := by
  rw [← List.length_eq_zero_iff, bits_length]
  cases prior : cursor.prior <;> simp [Cursor.isEmpty, Cursor.remaining, prior] <;> omega

theorem start_sound {input : List UInt8} {cursor : Cursor}
    (success : start input = some cursor) : StartWire input cursor := by
  unfold start at success
  cases wire : input.reverse with
  | nil => simp [wire] at success
  | cons last prior =>
    simp only [wire] at success
    split at success
    · cases success
    · rename_i nonzero
      cases success
      have bytes : input = prior.reverse ++ [last] := by
        simpa using congrArg List.reverse wire
      have below : last.toNat.log2 < 8 := (Nat.log2_lt nonzero).mpr last.toNat_lt_size
      exact ⟨prior.reverse, last, last.toNat.log2, bytes, below,
        (Nat.log2_eq_iff nonzero).mp rfl |>.1, (Nat.log2_eq_iff nonzero).mp rfl |>.2,
        by simp⟩

private theorem next_sound {cursor rest : Cursor} {bit : Bit}
    (success : next cursor = some (bit, rest)) : cursor.bits = bit :: rest.bits := by
  obtain ⟨byte, count, prior⟩ := cursor
  cases count with
  | zero =>
    cases prior with
    | nil => cases success
    | cons b bs =>
      cases success
      simp [Cursor.bits, msbBits]
  | succ count =>
    cases success
    simp [Cursor.bits, msbBits]

private theorem value_lt (bits : List Bit) : Bit.bitsToNatMSB bits < 2 ^ bits.length := by
  induction bits with
  | nil => decide
  | cons bit bits ih =>
    cases bit <;> simp [Bit.bitsToNatMSB, Nat.pow_succ] <;> omega

private theorem readLoop_sound {width acc value : Nat} {cursor rest : Cursor}
    (success : readLoop width cursor acc = some (value, rest)) :
    ∃ field, cursor.bits = field ++ rest.bits ∧ field.length = width ∧
      value = acc * 2 ^ width + Bit.bitsToNatMSB field := by
  induction width generalizing cursor acc with
  | zero =>
    cases success
    exact ⟨[], rfl, rfl, by simp [Bit.bitsToNatMSB]⟩
  | succ width ih =>
    cases takeBit : next cursor with
    | none => simp [readLoop, takeBit, bind, Option.bind] at success
    | some pair =>
      obtain ⟨bit, afterBit⟩ := pair
      simp only [readLoop, takeBit, bind, Option.bind] at success
      obtain ⟨tail, shape, length, algebra⟩ := ih success
      refine ⟨bit :: tail, by rw [next_sound takeBit, shape]; rfl, by simp [length], ?_⟩
      rw [algebra]
      simp [Bit.bitsToNatMSB, length, Nat.pow_succ', Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem read_sound {width value : Nat} {cursor rest : Cursor}
    (success : read width cursor = some (value, rest)) :
    ∃ field, cursor.bits = field ++ rest.bits ∧ field.length = width ∧
      value = Bit.bitsToNatMSB field ∧ value < 2 ^ width ∧
      cursor.remaining = width + rest.remaining := by
  obtain ⟨field, shape, length, algebra⟩ := readLoop_sound success
  simp only [Nat.zero_mul, Nat.zero_add] at algebra
  refine ⟨field, shape, length, algebra, ?_, ?_⟩
  · rw [algebra, ← length]
    exact value_lt field
  · rw [← bits_length cursor, ← bits_length rest, shape, List.length_append, length]

end Silmaril.Proofs.Formats.Compression.Zstd.ReverseBits
