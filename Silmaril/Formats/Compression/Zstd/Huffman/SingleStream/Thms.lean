module

public import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Huffman.SingleStream.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.SingleStream

/-- Success validates the input weights and assigns exact canonical codes
    in RFC rank order across the complete slot interval. -/
theorem build_sound {limits : DirectWeights.Limits} {tree : DirectWeights.Tree} {table : Table}
    (success : build limits tree = .ok table) : tree.Valid limits ∧ TableWire tree table :=
  Proofs.Formats.Compression.Zstd.Huffman.SingleStream.build_sound success

/-- Nonempty aligned code intervals stay in range and are pairwise disjoint. -/
theorem table_intervals {tree : DirectWeights.Tree} {table : Table} (wire : TableWire tree table) :
    (∀ entry ∈ table.entries, 0 < entry.width ∧ entry.width ≤ table.depth ∧
      entry.finish table.depth ≤ 2 ^ table.depth) ∧
    table.entries.Pairwise (fun left right => left.finish table.depth ≤ right.start table.depth) :=
  Proofs.Formats.Compression.Zstd.Huffman.SingleStream.table_intervals wire

/-- A bounded caller may reuse the same table for independent streams.
    Each success gives the exact symbol count and exhausts its own stream. -/
theorem readStream_sound {table : Table} {expected : Nat} {input out : List UInt8}
    (success : Internal.readStream table expected input = .ok out) :
    out.length = expected ∧ ∃ cursor, ReverseBits.StartWire input cursor ∧
      StreamWire table.entries cursor.bits out :=
  Proofs.Formats.Compression.Zstd.Huffman.SingleStream.readStream_sound success

/-- Accepting a stream accounts for the marker and every payload bit with
    the canonical table, and produces exactly the requested symbol count. -/
theorem decode_sound {limits : Limits} {tree : DirectWeights.Tree} {expected : Nat}
    {input out : List UInt8} (success : decode limits tree expected input = .ok out) :
    input.length ≤ limits.inputBytes ∧ out.length = expected ∧ expected ≤ limits.outputSymbols ∧
    tree.Valid limits.tree ∧
    ∃ table cursor, TableWire tree table ∧ ReverseBits.StartWire input cursor ∧
      StreamWire table.entries cursor.bits out :=
  Proofs.Formats.Compression.Zstd.Huffman.SingleStream.decode_sound success

end Silmaril.Formats.Compression.Zstd.Huffman.SingleStream
