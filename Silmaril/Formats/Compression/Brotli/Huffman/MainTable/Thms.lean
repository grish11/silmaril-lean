module

public import Silmaril.Formats.Compression.Brotli.Huffman.MainTable.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Huffman.MainTable.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.MainTable

/-- Installation retains the exact expanded vector, the original wire
    witness and its cursor, and the complete RFC code space. -/
theorem read_sound {limits : MainLengths.Limits} {alphabet : Nat}
    {secondary : CodeLengths.Table} {before after : LSBReader}
    {input : List Bool} {table : Table} (rep : before.Rep input) (count : before.count < 8)
    (read : read limits alphabet secondary before = .ok (table, after)) :
    MainLengths.read limits alphabet secondary before = .ok (table.lengths, after) ∧
    table.lengths.length = alphabet ∧ table.decoder.alphabetSize = alphabet ∧ table.decoder.maxBits = 15 ∧
    isCompleteCode table.lengths 15 = true ∧ 0 < alphabet ∧ alphabet ≤ 704 ∧ alphabet ≤ limits.alphabet ∧
    ∃ used suffix, MainLengths.RunsWire secondary MainLengths.History.start alphabet 32768 used table.lengths ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Huffman.MainTable.read_sound rep count read

/-- A successfully expanded vector is admissible to the shared canonical
    constructor, with no further cursor movement. -/
theorem read_after_lengths {limits : MainLengths.Limits} {alphabet : Nat}
    {secondary : CodeLengths.Table} {before after : LSBReader} {input : List Bool}
    {lengths : List Nat} (rep : before.Rep input) (count : before.count < 8)
    (expanded : MainLengths.read limits alphabet secondary before = .ok (lengths, after)) :
    ∃ table, read limits alphabet secondary before = .ok (table, after) ∧ table.lengths = lengths :=
  Proofs.Formats.Compression.Brotli.Huffman.MainTable.read_after_lengths rep count expanded

/-- The canonical code is the first code of its width plus the rank
    among earlier symbols of that width. Zero widths leave ordinal slots
    in the table and have no code. Out-of-range ordinals have no entry. -/
theorem Table.ordinal (table : Table) (ordinal : Nat) :
    let expected := table.lengths[ordinal]?.map fun depth =>
      ({ symbol := ordinal, length := depth,
         code := if depth = 0 then 0 else
           (nextCode (countByLength table.lengths 15)).getD (depth - 1) 0 +
             (table.lengths.take ordinal).count depth } : CodeEntry)
    table.decoder.entries[ordinal]? = expected ∧
      table.decoder.encodeSymbol ordinal = expected.bind
        (fun entry => if entry.length = 0 then none else some (entry.code, entry.length)) :=
  Proofs.Formats.Compression.Brotli.Huffman.MainTable.Table.ordinal table ordinal

end Silmaril.Formats.Compression.Brotli.Huffman.MainTable
