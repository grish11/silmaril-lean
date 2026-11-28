module

import Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Defs
meta import Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Defs

open Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription

public def main (args : List String) : IO UInt32 := do
  let [source, slotsPath, suffixPath, bytes, symbols, depth] := args | return 2
  let [some b, some n, some d] := [bytes, symbols, depth].map String.toNat? | return 2
  let input := (← IO.FS.readBinFile source).data.toList
  match readTable ⟨b, ⟨n, d⟩⟩ input with
  | .error reason =>
    IO.println (reprStr reason)
    return 3
  | .ok (result, table) =>
    let mut rows := Array.replicate (2 * 2 ^ table.depth) (0 : UInt8)
    for entry in table.entries do
      for slot in [entry.start table.depth : entry.finish table.depth] do
        rows := (rows.set! (2 * slot) entry.width.toUInt8).set! (2 * slot + 1) entry.symbol.toUInt8
    IO.FS.writeBinFile slotsPath ⟨rows⟩
    IO.FS.writeBinFile suffixPath ⟨result.rest.toArray⟩
    let mode := match result.mode with | .direct => "direct" | .fse => "fse"
    IO.println s!"{mode} {result.consumed} {result.tree.depth} {result.tree.weights.length}"
    IO.println (String.intercalate " " (result.tree.weights.map toString))
    return 0
