module

public import Silmaril.Formats.Compression.Zstd.FseTable.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.FseTable.Contracts

/-! # Exact normalized distributions and safe FSE transitions -/

public section

namespace Silmaril.Formats.Compression.Zstd.FseTable

/-- The accepted distribution fits the caps. The table follows the state
    walk, covers the entire state space, and has exact symbol multiplicities. -/
theorem build_sound {limits : Limits} {dist : Distribution} {table : Table}
    (success : build limits dist = .ok table) :
    dist.Valid limits ∧ TableWire dist table ∧ table.WellFormed dist :=
  Proofs.Formats.Compression.Zstd.FseTable.build_sound success

/-- Indexing the table agrees with the symbol placement and ordinal formula. -/
theorem row_agrees {dist : Distribution} {table : Table} {state : Nat} {row : Row}
    (wire : TableWire dist table) (lookup : table.rows[state]? = some row) :
    ∃ symbols symbol, LayoutWire dist symbols ∧ symbols[state]? = some symbol ∧
      row = rowFor dist symbols state symbol :=
  Proofs.Formats.Compression.Zstd.FseTable.row_agrees wire lookup

/-- A selected state, its symbol and every next state selected by its
    fixed-width bit field are within their respective bounds. -/
theorem state_bounds {dist : Distribution} {table : Table} {state extra : Nat} {row : Row}
    (wellFormed : table.WellFormed dist) (lookup : table.rows[state]? = some row)
    (field : extra < 2 ^ row.bits) :
    state < 2 ^ table.log ∧ row.symbol < dist.weights.length ∧ row.bits ≤ table.log ∧
      row.baseline + extra < 2 ^ table.log :=
  Proofs.Formats.Compression.Zstd.FseTable.state_bounds wellFormed lookup field

/-- The table size fits the caller's accuracy-log cap, intersected with 9. -/
theorem table_size_le {limits : Limits} {dist : Distribution} {table : Table}
    (success : build limits dist = .ok table) : table.rows.length ≤ 2 ^ limits.logCap :=
  Proofs.Formats.Compression.Zstd.FseTable.table_size_le success

/-- Predefined mode consumes no table bytes. The resulting table has the
    validated RFC distribution for the selected alphabet. -/
theorem selectPredefined_sound {limits : Limits} {alphabet : Alphabet} {mode : UInt8}
    {input rest : List UInt8} {table : Table}
    (success : selectPredefined limits alphabet mode input = .ok (table, rest)) :
    mode = 0 ∧ rest = input ∧ (predefined alphabet).Valid limits ∧
      TableWire (predefined alphabet) table ∧ table.WellFormed (predefined alphabet) :=
  Proofs.Formats.Compression.Zstd.FseTable.selectPredefined_sound success

end Silmaril.Formats.Compression.Zstd.FseTable
