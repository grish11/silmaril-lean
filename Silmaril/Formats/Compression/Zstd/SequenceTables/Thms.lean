module

public import Silmaril.Formats.Compression.Zstd.SequenceTables.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.SequenceTables.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.SequenceTables

/-- Resolving one mode consumes its exact description and leaves the suffix intact. -/
theorem resolveTable_sound {alphabet : FseTable.Alphabet} {mode : Nat}
    {input rest : List UInt8} {table : Table}
    (success : resolveTable alphabet mode input = .ok (table, rest)) :
    ∃ used, input = used ++ rest ∧ TableWire alphabet mode used rest table :=
  Proofs.Formats.Compression.Zstd.SequenceTables.resolveTable_sound success

/-- The caller's caps hold and each table description occupies its exact
    slice in the input. The suffix is the entire remaining bitstream. -/
theorem resolve_sound {limits : Limits} {input : List UInt8} {result : Section}
    (success : resolve limits input = .ok result) :
    input.length ≤ limits.inputBytes ∧ result.count ≤ limits.sequences ∧ SectionWire input result :=
  Proofs.Formats.Compression.Zstd.SequenceTables.resolve_sound success

/-- Every resolved FSE row stays within its alphabet and table. A value read
    at the row's bit width selects a next state in the same table. -/
theorem fse_state_bounds {alphabet : FseTable.Alphabet} {mode state extra : Nat}
    {used rest : List UInt8} {table : FseTable.Table} {row : FseTable.Row}
    (wire : TableWire alphabet mode used rest (.fse table))
    (lookup : table.rows[state]? = some row) (field : extra < 2 ^ row.bits) :
    table.log ≤ (tableLimits alphabet).accuracyLog ∧ state < 2 ^ table.log ∧
      row.symbol < (tableLimits alphabet).symbols ∧ row.bits ≤ table.log ∧
      row.baseline + extra < 2 ^ table.log :=
  Proofs.Formats.Compression.Zstd.SequenceTables.fse_state_bounds wire lookup field

/-- Dropping just the header and table bytes recovers the unread stream. -/
theorem suffix_exact {input : List UInt8} {result : Section} (wire : SectionWire input result) :
    input.drop (input.length - result.bitstream.length) = result.bitstream :=
  Proofs.Formats.Compression.Zstd.SequenceTables.suffix_exact wire

end Silmaril.Formats.Compression.Zstd.SequenceTables
