module

import Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Defs
meta import Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Defs

open Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights

public def main (args : List String) : IO UInt32 := do
  let [source, destination, bytes, symbols, depth] := args | return 2
  let [some b, some s, some d] := [bytes, symbols, depth].map String.toNat? | return 2
  let input := (← IO.FS.readBinFile source).data.toList
  match read ⟨b, s, d⟩ input with
  | .error reason =>
    IO.println (reprStr reason)
    return 3
  | .ok result =>
    IO.FS.writeBinFile destination ⟨result.rest.toArray⟩
    IO.println s!"{result.consumed} {result.tree.depth} {result.tree.weights.length}"
    IO.println (String.intercalate " " (result.tree.weights.map toString))
    return 0
