module

public import Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.ContextMap.Decode.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.ContextMap.Decode

theorem RunWire.bounds {trees rleMax value count : Nat} {table : Huffman.Description.Table}
    {bits : List Bool} (wire : RunWire trees rleMax table bits value count) (treesPositive : 0 < trees) :
    value < trees ∧ 0 < count :=
  Proofs.Formats.Compression.Brotli.ContextMap.Decode.RunWire.bounds wire treesPositive

theorem RunsWire.bounds {trees rleMax slots work : Nat} {table : Huffman.Description.Table}
    {bits : List Bool} {positions : List Nat}
    (wire : RunsWire trees rleMax table slots work bits positions) (treesPositive : 0 < trees) :
    positions.length = slots ∧ work ≤ slots ∧ ∀ index ∈ positions, index < trees :=
  Proofs.Formats.Compression.Brotli.ContextMap.Decode.RunsWire.bounds wire treesPositive

/-- The bounded initial list yields the same inverse-MTF outputs as
    the full 256-entry list specified by RFC 7932. -/
theorem MtfWire.fullTable {trees : Nat} {positions values : List Nat}
    (wire : MtfWire (List.range trees) positions values) (bound : trees ≤ 256) :
    MtfWire (List.range 256) positions values :=
  Proofs.Formats.Compression.Brotli.ContextMap.Decode.MtfWire.fullTable wire bound

/-- The final index set is precisely the declared tree range. The work count bounds all coded symbol reads. -/
theorem Wire.valid {entries work : Nat} {bits : List Bool} {result : Map}
    (wire : Wire entries work bits result) :
    result.indices.length = entries ∧ work ≤ entries ∧ 1 ≤ result.treeCount ∧
      result.treeCount ≤ 256 ∧ (∀ index, index ∈ result.indices ↔ index < result.treeCount) :=
  Proofs.Formats.Compression.Brotli.ContextMap.Decode.Wire.valid wire

/-- Success witnesses every original bit under a shared cap, with
    exact entry and symbol limits and the untouched following bits. -/
theorem read_sound {kind : Kind} {types : Nat} {limits : Limits} {before after : LSBReader}
    {input : List Bool} {result : Map} (rep : before.Rep input) (count : before.count < 8)
    (read : Silmaril.Formats.Compression.Brotli.ContextMap.Decode.read kind types limits before = .ok (result, after)) :
    1 ≤ types ∧ types ≤ 256 ∧ kind.extent types ≤ limits.entries ∧
    ∃ work used suffix, work ≤ limits.symbols ∧ Wire (kind.extent types) work used result ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.ContextMap.Decode.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.ContextMap.Decode
