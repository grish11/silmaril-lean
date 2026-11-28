module

public import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol.Defs
import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Huffman.CodeLengthSymbol

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol
open Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol.Internal


private theorem commit_sound {table : Brotli.Huffman.CodeLengths.Table} {widthLimit symbol result : Nat}
    {before after : LSBReader} {input : List Bool} (rep : before.Rep input) (count : before.count < 8)
    (cap : widthLimit ≤ 5) (checked : commit table widthLimit symbol before = .ok (result, after)) :
    ∃ used suffix, Wire table result used ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ widthLimit := by
  unfold commit at checked
  split at checked <;> try contradiction
  rename_i symbolBound
  split at checked <;> try contradiction
  rename_i code width assigned
  split at checked <;> try contradiction
  rename_i widthBound
  split at checked <;> try contradiction
  rename_i value next readBits
  split at checked <;> try contradiction
  rename_i wireBits
  cases checked
  obtain ⟨suffix, split, nextRep, _, offset, nextCount⟩ := LSBReader.readBits_sound rep count readBits
  exact ⟨natBits value width, suffix, ⟨by omega, code, width, assigned, by omega, wireBits⟩,
    split, nextRep, nextCount ▸ Nat.mod_lt _ (by decide), by simpa only [natBits_length] using offset,
    by rw [natBits_length]; omega⟩

theorem read_sound {table : Brotli.Huffman.CodeLengths.Table} {limit symbol : Nat}
    {before after : LSBReader} {input : List Bool} (rep : before.Rep input) (count : before.count < 8)
    (checked : read table limit before = .ok (symbol, after)) :
    ∃ used suffix, Wire table symbol used ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limit ∧ used.length ≤ 5 := by
  cases kind : table.codes with
  | singleton only =>
    simp only [Brotli.Huffman.CodeLengthSymbol.read, kind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at checked
    obtain ⟨rfl, rfl⟩ := checked
    obtain ⟨bound, code, _⟩ := Brotli.Huffman.CodeLengths.Table.singleton_code kind
    exact ⟨[], input, ⟨bound, 0, 0, code, by decide, rfl⟩, rfl, rep, count, by simp, by simp, by simp⟩
  | canonical codes =>
    simp only [Brotli.Huffman.CodeLengthSymbol.read, kind] at checked
    split at checked
    · split at checked
      · have cap : lookWidth limit before ≤ 5 := Nat.le_trans (Nat.min_le_left ..) (Nat.min_le_right ..)
        have budget : lookWidth limit before ≤ limit := Nat.le_trans (Nat.min_le_left ..) (Nat.min_le_left ..)
        obtain ⟨used, suffix, wire, split, rep', count', offset, extent⟩ := commit_sound rep count cap checked
        exact ⟨used, suffix, wire, split, rep', count', offset, Nat.le_trans extent budget, Nat.le_trans extent cap⟩
      · contradiction
    · contradiction

end Silmaril.Proofs.Formats.Compression.Brotli.Huffman.CodeLengthSymbol
