module

public import Silmaril.Formats.Compression.Brotli.Huffman.Simple.Defs
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Huffman.Simple

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman.Simple
open Silmaril.Formats.Compression.Brotli.Huffman.Simple.Internal

theorem alphabetWidth_minimal {alphabet : Nat} (positive : 0 < alphabet) :
    alphabet ≤ 2 ^ alphabetWidth alphabet ∧ ∀ k < alphabetWidth alphabet, 2 ^ k < alphabet := by
  unfold alphabetWidth
  split
  · rename_i one
    have : alphabet = 1 := by omega
    subst alphabet
    simp
  · rename_i many
    have nz : alphabet - 1 ≠ 0 := by omega
    have fits := (Nat.log2_lt (k := (alphabet - 1).log2 + 1) nz).mp (Nat.lt_succ_self _)
    refine ⟨by omega, ?_⟩
    intro k smaller
    have power := (Nat.le_log2 (k := k) nz).mp (by omega)
    omega

private theorem width_le {alphabet : Nat} (fits : alphabet ≤ 704) : alphabetWidth alphabet ≤ 10 := by
  unfold alphabetWidth
  split
  · decide
  · rename_i many
    have depth := (Nat.log2_lt (k := 10) (n := alphabet - 1) (by omega)).mpr (by omega)
    omega

private theorem encoded_symbols_size (symbols : List Nat) (width : Nat) :
    (symbols.flatMap fun symbol => natBits symbol width).length = symbols.length * width := by
  induction symbols with
  | nil => simp
  | cons symbol symbols ih =>
    simp [List.flatMap_cons, natBits_length, ih, Nat.add_mul, Nat.add_comm]

theorem Wire.bit_bound {alphabet : Nat} {body : List Bool} {shape : Shape}
    (wire : Wire alphabet body shape) (fits : alphabet ≤ 704) : body.length ≤ 43 := by
  have depth := width_le fits
  rw [wire.1]
  unfold Shape.bits
  simp only [List.length_append, natBits_length, encoded_symbols_size]
  cases shape <;> simp [Shape.symbols, Shape.treeBits] <;> omega

private structure Advance (before after : Cursor) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.reader.Rep suffix
  count : after.reader.count < 8
  offset : after.reader.totalRead = before.reader.totalRead + used.length
  budget : before.remaining = after.remaining + used.length

private theorem Advance.refl {cursor : Cursor} {input : List Bool} (rep : cursor.reader.Rep input)
    (count : cursor.reader.count < 8) : Advance cursor cursor input [] input :=
  ⟨rfl, rep, count, by simp, by simp⟩

private theorem Advance.trans {before middle after : Cursor}
    {input first rest second suffix : List Bool}
    (a : Advance before middle input first rest) (b : Advance middle after rest second suffix) :
    Advance before after input (first ++ second) suffix := by
  refine ⟨by rw [a.split, b.split, List.append_assoc], b.rep, b.count, ?_, ?_⟩
  · simp only [List.length_append, b.offset, a.offset]
    omega
  · simp only [List.length_append, a.budget, b.budget]
    omega

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem take_sound {width value : Nat} {before after : Cursor} {input : List Bool}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : take before width = .ok (value, after)) :
    value < 2 ^ width ∧ ∃ suffix, Advance before after input (natBits value width) suffix := by
  unfold take at read
  split at read <;> try contradiction
  rename_i cap
  split at read <;> try contradiction
  rename_i n cursor actual
  cases read
  obtain ⟨suffix, split, rep', fits, offset, count'⟩ := LSBReader.readBits_sound rep count actual
  refine ⟨fits, suffix, split, rep', count' ▸ Nat.mod_lt _ (by decide), ?_, ?_⟩
  · simpa only [natBits_length] using offset
  · simp only [natBits_length]
    omega

private theorem readSymbols_sound {width count : Nat} {before after : Cursor}
    {symbols : List Nat} {input : List Bool} (rep : before.reader.Rep input) (buffered : before.reader.count < 8)
    (read : readSymbols width count before = .ok (symbols, after)) :
    symbols.length = count ∧
    ∃ suffix, Advance before after input (symbols.flatMap fun symbol => natBits symbol width) suffix := by
  induction count generalizing before after input symbols with
  | zero =>
    simp only [readSymbols, Except.ok.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨rfl, input, .refl rep buffered⟩
  | succ count ih =>
    simp only [readSymbols] at read
    obtain ⟨⟨symbol, current⟩, field, next⟩ := bind_ok read
    obtain ⟨⟨rest, last⟩, fields, done⟩ := bind_ok next
    cases done
    obtain ⟨_, middle, first⟩ := take_sound rep buffered field
    obtain ⟨size, suffix, second⟩ := ih first.rep first.count fields
    exact ⟨by simp [size], suffix, first.trans second⟩

private theorem finish_sound {symbols : List Nat} {before after : Cursor}
    {shape : Shape} {input : List Bool} (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : finish symbols before = .ok (shape, after)) :
    shape.symbols = symbols ∧ ∃ suffix, Advance before after input shape.treeBits suffix := by
  unfold finish at read
  split at read
  · cases read
    exact ⟨rfl, input, .refl rep count⟩
  · cases read
    exact ⟨rfl, input, .refl rep count⟩
  · cases read
    exact ⟨rfl, input, .refl rep count⟩
  · obtain ⟨⟨tree, cursor⟩, field, next⟩ := bind_ok read
    obtain ⟨width, suffix, advance⟩ := take_sound rep count field
    have kinds : tree = 0 ∨ tree = 1 := by omega
    rcases kinds with rfl | rfl <;> cases next <;> exact ⟨rfl, suffix, advance⟩
  · contradiction

private theorem check_shape {alphabet : Nat} {shape : Shape} {checked : Checked alphabet}
    (read : check alphabet shape = .ok checked) : checked.shape = shape := by
  unfold check at read
  split at read <;> try contradiction
  split at read <;> cases read <;> rfl

theorem read_sound {alphabet limit : Nat} {before after : LSBReader}
    {input : List Bool} {checked : Checked alphabet} (rep : before.Rep input) (count : before.count < 8)
    (read : read alphabet limit before = .ok (checked, after)) :
    ∃ used suffix, Wire alphabet used checked.shape ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ limit := by
  unfold Formats.Compression.Brotli.Huffman.Simple.read at read
  obtain ⟨⟨extra, cursor⟩, size, next⟩ := bind_ok read
  obtain ⟨⟨symbols, middle⟩, fields, next⟩ := bind_ok next
  obtain ⟨⟨shape, last⟩, shapeRead, next⟩ := bind_ok next
  obtain ⟨result, validation, done⟩ := bind_ok next
  cases done
  obtain ⟨_, body, first⟩ := take_sound rep count size
  obtain ⟨symbolCount, treeBits, second⟩ := readSymbols_sound first.rep first.count fields
  obtain ⟨symbolsMatch, suffix, third⟩ := finish_sound second.rep second.count shapeRead
  have shapeMatch := check_shape validation
  rw [← shapeMatch] at symbolsMatch
  rw [← shapeMatch] at third
  have all := first.trans (second.trans third)
  refine ⟨_, suffix, ⟨?_, checked.distinct, checked.bounded⟩, all.split, all.rep, all.count, all.offset, ?_⟩
  · simp [Shape.bits, symbolsMatch, symbolCount]
  · have fits := all.budget
    dsimp at fits
    omega

end Silmaril.Proofs.Formats.Compression.Brotli.Huffman.Simple
