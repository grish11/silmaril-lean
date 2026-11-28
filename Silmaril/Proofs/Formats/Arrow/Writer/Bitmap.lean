module

public import Silmaril.Formats.Arrow.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.Writer.Buffers
import Silmaril.Prelude.Bytes.Thms
import Init.Data.List.Nat.TakeDrop
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.Writer

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Writer

private theorem lowBits_at (bits : List Bool) (index : Nat) (bound : index < bits.length) :
    (lowBits bits).testBit index = bits[index] := by
  induction bits generalizing index with
  | nil => simp at bound
  | cons bit bits ih =>
    cases index with
    | zero =>
      cases bit <;> simp [lowBits, Nat.testBit_zero] <;> omega
    | succ index =>
      rw [lowBits, Nat.testBit_add_one, List.getElem_cons_succ]
      have div : ((if bit then 1 else 0) + 2 * lowBits bits) / 2 = lowBits bits := by
        cases bit <;> simp <;> omega
      rw [div]
      exact ih index (by simpa using bound)

theorem bitmapWords_length (bits : List Bool) :
    (bitmapWords bits).length = (bits.length + 7) / 8 := by
  induction bits using bitmapWords.induct with
  | case1 bits empty =>
    have eq : bits = [] := by simpa using empty
    rw [eq, bitmapWords]
    rfl
  | case2 bits nonempty ih =>
    have pos : 0 < bits.length := by cases bits <;> simp_all
    rw [bitmapWords, ite_eq_right nonempty, List.length_cons, ih, List.length_drop]
    omega

private theorem bitmapWord_at (bits : List Bool) (index : Nat) (bound : index < bits.length) :
    ∃ word, (bitmapWords bits)[index / 8]? = some word ∧
      word.testBit (index % 8) = bits[index] := by
  induction bits using bitmapWords.induct generalizing index with
  | case1 bits empty =>
    have eq : bits = [] := by simpa using empty
    simp [eq] at bound
  | case2 bits nonempty ih =>
    rw [bitmapWords, ite_eq_right nonempty]
    by_cases small : index < 8
    · have bitBound : index < (bits.take 8).length := by simp; omega
      refine ⟨lowBits (bits.take 8), ?_, ?_⟩
      · simp [Nat.div_eq_of_lt small]
      · rw [Nat.mod_eq_of_lt small, lowBits_at _ _ bitBound, List.getElem_take]
    · have tailBound : index - 8 < (bits.drop 8).length := by simp; omega
      have quotient : index / 8 = (index - 8) / 8 + 1 := by omega
      have remainder : index % 8 = (index - 8) % 8 := by omega
      obtain ⟨word, found, value⟩ := ih (index - 8) tailBound
      refine ⟨word, ?_, ?_⟩
      · simpa [quotient] using found
      · rw [remainder, value, List.getElem_drop]
        simp [show 8 + (index - 8) = index by omega]

private theorem emitOctets (words : List Nat) :
    (emitWords 1 words).toList = words.map UInt8.ofNat := by
  rw [emitWords_bytes]
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [List.flatMap_cons, List.map_cons, ih]
    simp [KBytes.unpack]

theorem emitBitmap_length {α : Type} (slots : List (Option α)) :
    (emitBitmap slots).len = (slots.length + 7) / 8 := by
  simp [emitBitmap, emitWords_length, bitmapWords_length]

theorem emitBitmap_valid {α : Type} (slots : List (Option α)) (index : Nat)
    (bound : index < slots.length) :
    Body.validAt (emitBitmap slots) index = some slots[index].isSome := by
  have nonempty : (emitBitmap slots).len ≠ 0 := by rw [emitBitmap_length]; omega
  rw [Body.validAt, ite_eq_right nonempty]
  unfold emitBitmap
  rw [KBytes.get?_eq _ (emitWords_wf _ _)]
  obtain ⟨word, found, value⟩ := bitmapWord_at (slots.map Option.isSome) index (by simpa using bound)
  rw [emitOctets, List.getElem?_map, found]
  simp only [Option.map_some, UInt8.toNat_ofNat', Nat.testBit_mod_two_pow,
    show index % 8 < 8 by omega, decide_true, Bool.true_and]
  simpa using value

end Silmaril.Proofs.Formats.Arrow.Writer
