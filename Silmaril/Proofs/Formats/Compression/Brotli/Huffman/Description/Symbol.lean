module

public import Silmaril.Formats.Compression.Brotli.Huffman.Description.Defs
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Huffman.Description

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman.Description

theorem readBounded_sound {table : Table} {bitLimit symbol : Nat}
    {before after : LSBReader} {input : List Bool} (rep : before.Rep input)
    (count : before.count < 8) (read : table.readBounded bitLimit before = .ok (symbol, after)) :
    ∃ code width suffix, table.codeFor symbol = some (code, width) ∧
      width ≤ 15 ∧ width ≤ bitLimit ∧ input = msbBits code width ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + width := by
  unfold Table.readBounded at read
  revert read
  generalize Internal.findBounded table bitLimit before = found
  intro read
  cases found with
  | error => contradiction
  | ok candidate =>
    simp only [bind, Except.bind] at read
    split at read <;> try contradiction
    rename_i code width assigned
    split at read <;> try contradiction
    rename_i widthBound
    split at read <;> try contradiction
    rename_i cap
    split at read <;> try contradiction
    rename_i value cursor actual
    split at read <;> try contradiction
    rename_i sameBits
    cases read
    obtain ⟨suffix, split, rep', _, offset, count'⟩ := LSBReader.readBits_sound rep count actual
    exact ⟨code, width, suffix, assigned, by omega, by omega, sameBits ▸ split,
      rep', count' ▸ Nat.mod_lt _ (by decide), offset⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Huffman.Description
