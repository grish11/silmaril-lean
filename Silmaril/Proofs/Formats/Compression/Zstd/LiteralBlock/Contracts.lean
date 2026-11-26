module

public import Silmaril.Formats.Compression.Zstd.LiteralBlock.Defs

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.LiteralBlock

open Silmaril.Formats.Compression.Zstd (Header blockMaximum)
open Silmaril.Formats.Compression.Zstd.LiteralBlock
open Silmaril.Formats.Compression.Zstd.LiteralBlock.Internal

private theorem readSize_sound {first : UInt8} {input rest : List UInt8} {size : Nat}
    (h : readSize first input = .ok (size, rest)) :
    ∃ tail, SizeWire (first :: tail) size ∧ input = tail ++ rest := by
  by_cases medium : first.toNat / 4 % 4 = 1
  · cases input with
    | nil => simp [readSize, medium] at h
    | cons byte rest =>
      simp [readSize, medium] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[byte], .medium first byte medium, rfl⟩
  · by_cases long : first.toNat / 4 % 4 = 3
    · cases input with
      | nil => simp [readSize, long] at h
      | cons lo tail =>
        cases tail with
        | nil => simp [readSize, long] at h
        | cons hi rest =>
          simp [readSize, long] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨[lo, hi], .long first lo hi long, rfl⟩
    · simp [readSize, medium, long] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], .short first (by omega), rfl⟩

theorem parseLiterals_sound {limit : Nat} {input rest : List UInt8} {literals : Literals}
    (h : parseLiterals limit input = .ok (literals, rest)) :
    LiteralsWire input literals rest ∧ literals.size ≤ limit := by
  cases input with
  | nil => cases h
  | cons first tail =>
    simp only [parseLiterals] at h
    split at h
    · simp [throw, bind, Except.bind] at h
    · rename_i notHuffman
      split at h
      · simp [throw, bind, Except.bind] at h
      · rename_i notTreeless
        cases length : readSize first tail with
        | error error => simp [length, bind, Except.bind] at h
        | ok pair =>
          obtain ⟨size, body⟩ := pair
          obtain ⟨sizeTail, wire, shape⟩ := readSize_sound length
          simp only [length, bind, Except.bind] at h
          split at h
          · simp [throw] at h
          · rename_i fits
            split at h
            · rename_i raw
              simp only [List.splitAt_eq] at h
              split at h
              · rename_i taken
                cases h
                refine ⟨?_, by simpa [Literals.size, taken] using Nat.le_of_not_gt fits⟩
                have bytes : tail = sizeTail ++ body.take size ++ body.drop size := by
                  rw [shape, List.append_assoc, List.take_append_drop]
                rw [bytes]
                exact .raw raw (by rwa [taken])
              · cases h
            · rename_i rle
              cases body with
              | nil => cases h
              | cons byte rest =>
                cases h
                rw [shape]
                exact ⟨.rle (by omega) wire, Nat.le_of_not_gt fits⟩

theorem readSequenceCount_sound {input rest : List UInt8} {count : Nat}
    (h : readSequenceCount input = .ok (count, rest)) :
    ∃ encoded, input = encoded ++ rest ∧ SequenceCountWire encoded count := by
  cases input with
  | nil => cases h
  | cons first tail =>
    simp only [readSequenceCount] at h
    split at h
    · next small =>
      cases h
      exact ⟨[first], rfl, .short first small⟩
    · rename_i notSmall
      split at h
      · next long =>
        have eq : first = 255 := UInt8.toNat_inj.mp long
        cases tail with
        | nil => cases h
        | cons lo tail =>
          cases tail with
          | nil => cases h
          | cons hi rest =>
            cases h
            exact ⟨[255, lo, hi], by rw [eq]; rfl, .long lo hi⟩
      · next notLong =>
        have bound := first.toNat_lt_size
        change first.toNat < 256 at bound
        cases tail with
        | nil => cases h
        | cons byte rest =>
          cases h
          exact ⟨[first, byte], rfl, .medium first byte (by omega) (by omega)⟩

private theorem fitsInput_sound {limit : Nat} {input : List UInt8}
    (h : fitsInput limit input = true) : input.length ≤ limit := by
  induction limit generalizing input with
  | zero => cases input <;> simp_all [fitsInput]
  | succ limit ih => cases input <;> simp_all [fitsInput]

theorem decode_sound {header : Header} {limit : Nat} {input out : List UInt8}
    (h : decode header limit input = .ok out) :
    ∃ literals, BlockWire input literals ∧ literals.expand = out ∧
      input.length ≤ blockMaximum header ∧
      out.length ≤ blockMaximum header ∧ out.length ≤ limit := by
  unfold decode at h
  split at h
  · cases h
  · rename_i extent
    have inputFits : input.length ≤ blockMaximum header :=
      fitsInput_sound (by simpa using extent)
    cases parsed : parseLiterals (min (blockMaximum header) limit) input with
    | error error => simp [parsed, bind, Except.bind] at h
    | ok pair =>
      obtain ⟨literals, sequences⟩ := pair
      simp only [parsed, bind, Except.bind] at h
      cases countRead : readSequenceCount sequences with
      | error error => simp [countRead] at h
      | ok pair =>
        obtain ⟨count, tail⟩ := pair
        simp only [countRead] at h
        split at h
        · cases h
        · rename_i zero
          have countZero : count = 0 := by omega
          cases tail with
          | cons byte rest => cases h
          | nil =>
            cases h
            obtain ⟨literalWire, bound⟩ := parseLiterals_sound parsed
            obtain ⟨encoded, eq, seqWire⟩ := readSequenceCount_sound countRead
            simp only [List.append_nil] at eq
            have size : literals.expand.length = literals.size := by
              cases literals <;> simp [Literals.expand, Literals.size]
            have bounds := Nat.le_min.mp bound
            exact ⟨literals, .ofSections literalWire (by rwa [eq, ← countZero]),
              rfl, inputFits, size ▸ bounds.1, size ▸ bounds.2⟩

end Silmaril.Proofs.Formats.Compression.Zstd.LiteralBlock
