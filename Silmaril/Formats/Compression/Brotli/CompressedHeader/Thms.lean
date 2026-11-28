module

public import Silmaril.Formats.Compression.Brotli.CompressedHeader.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.CompressedHeader.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.CompressedHeader

open Huffman.Description (Table)

theorem GroupWire.valid {alphabet count : Nat} {bits : List Bool} {tables : List Table}
    (wire : GroupWire alphabet count bits tables) :
    tables.length = count ∧ ∀ table ∈ tables, table.alphabetSize = alphabet :=
  Proofs.Formats.Compression.Brotli.CompressedHeader.GroupWire.valid wire

/-- Both map tree counts and the insert-and-copy block-type count
    select the corresponding group extent. Each table has its RFC alphabet. -/
theorem Wire.groups {work : Nat} {bits : List Bool} {header : Header} (wire : Wire work bits header) :
    ∀ group, (header.tables group).length = group.count header.initial header.literalMap header.distanceMap ∧
      ∀ table ∈ header.tables group, table.alphabetSize = group.alphabet header.initial.fields :=
  Proofs.Formats.Compression.Brotli.CompressedHeader.Wire.groups wire

theorem Wire.bounds {work : Nat} {bits : List Bool} {header : Header} (wire : Wire work bits header) :
    work ≤ header.mapEntries ∧ header.mapEntries ≤ 17408 ∧ 3 ≤ header.treeCount ∧ header.treeCount ≤ 768 :=
  Proofs.Formats.Compression.Brotli.CompressedHeader.Wire.bounds wire

/-- Success witnesses the original bits of the complete compressed
    header in order, with all caller caps and the exact payload suffix. -/
theorem read_sound {limits : Limits} {before after : LSBReader} {input : List Bool} {header : Header}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read limits before = .ok (header, after)) :
    header.mapEntries ≤ limits.mapEntries ∧ header.treeCount ≤ limits.trees ∧
    ∃ work used suffix, work ≤ limits.mapEntries ∧ Wire work used header ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.CompressedHeader.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.CompressedHeader
