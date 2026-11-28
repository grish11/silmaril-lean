module

public import Silmaril.Formats.Compression.Bits.BitstreamLemmas
import Silmaril.Raw.Formats.Compression.Bits.BitstreamFacts

public section

namespace Silmaril.Proofs.Formats.Compression.Bits

open Silmaril.Formats.Compression

private theorem readBit_rep {before after : LSBReader} {bits : List Bool} {bit : Bool}
    (rep : before.Rep bits) (read : before.readBit = some (bit, after)) :
    ∃ tail, bits = bit :: tail ∧ after.Rep tail := by
  cases bits with
  | nil =>
    have size : before.count + 8 * before.input.length = 0 := rep.bitsLeft
    have noInput : before.input = [] := List.length_eq_zero_iff.mp (by omega)
    simp [LSBReader.readBit, LSBReader.refill, show before.count = 0 by omega, noInput] at read
  | cons head tail =>
    obtain ⟨next, step, rest⟩ := rep.readBit
    rw [step] at read
    cases read
    exact ⟨tail, rfl, rest⟩

private theorem readBits_rep {width : Nat} {before after : LSBReader} {bits : List Bool} {value : Nat}
    (rep : before.Rep bits) (read : before.readBits width = some (value, after)) :
    ∃ tail, bits = natBits value width ++ tail ∧ after.Rep tail := by
  induction width generalizing before after bits value with
  | zero =>
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨bits, rfl, rep⟩
  | succ width ih =>
    simp only [LSBReader.readBits] at read
    split at read
    · contradiction
    rename_i bit middle first
    split at read
    · contradiction
    rename_i low next others
    cases read
    obtain ⟨tail, head, middleRep⟩ := readBit_rep rep first
    obtain ⟨rest, remaining, afterRep⟩ := ih middleRep others
    have order : natBits ((if bit then 1 else 0) + 2 * low) (width + 1) = bit :: natBits low width := by
      have parity : ((if bit then 1 else 0) + 2 * low) % 2 = (if bit then 1 else 0) := by
        cases bit <;> simp <;> omega
      have half : ((if bit then 1 else 0) + 2 * low) / 2 = low := by
        cases bit <;> simp <;> omega
      simp only [natBits, parity, half]
      cases bit <;> rfl
    exact ⟨rest, by rw [head, remaining, order, List.cons_append], afterRep⟩

theorem readBits_sound {width : Nat} {before after : LSBReader} {bits : List Bool} {value : Nat}
    (rep : before.Rep bits) (count : before.count < 8)
    (read : before.readBits width = some (value, after)) :
    ∃ tail, bits = natBits value width ++ tail ∧ after.Rep tail ∧ value < 2 ^ width ∧
      after.totalRead = before.totalRead + width ∧ after.count = (before.count + 7 * width) % 8 := by
  obtain ⟨tail, split, next⟩ := readBits_rep rep read
  exact ⟨tail, split, next, LSBReader.readBits_lt read, LSBReader.readBits_totalRead read,
    LSBReader.readBits_count width count read⟩

end Silmaril.Proofs.Formats.Compression.Bits
