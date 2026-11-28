module

import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Defs
meta import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Defs

open Silmaril.Formats.Compression.Zstd.Huffman
open SingleStream

private def treeLimits : DirectWeights.Limits := ⟨65, 129, 11⟩

public def main (args : List String) : IO UInt32 := do
  let [source, destination, mode, input, output] := args | return 2
  let [some i, some o] := [input, output].map String.toNat? | return 2
  let bytes := (← IO.FS.readBinFile source).data.toList
  let .ok parsed := DirectWeights.read treeLimits bytes | return 4
  if mode = "table" then
    let .ok table := build treeLimits parsed.tree | return 4
    let mut rows := Array.replicate (2 * 2 ^ table.depth) (0 : UInt8)
    for entry in table.entries do
      for slot in [entry.start table.depth : entry.finish table.depth] do
        rows := (rows.set! (2 * slot) entry.width.toUInt8).set! (2 * slot + 1) entry.symbol.toUInt8
    IO.FS.writeBinFile destination ⟨rows⟩
    return 0
  else
    let some expected := mode.toNat? | return 2
    match decode ⟨treeLimits, i, o⟩ parsed.tree expected parsed.rest with
    | .error reason =>
      IO.println (reprStr reason)
      return 3
    | .ok decoded =>
      IO.FS.writeBinFile destination ⟨decoded.toArray⟩
      return 0
