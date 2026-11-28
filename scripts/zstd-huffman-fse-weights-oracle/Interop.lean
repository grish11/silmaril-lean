module

import Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Defs
meta import Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Defs

open Silmaril.Formats.Compression.Zstd.Huffman.FseWeights

public def main (args : List String) : IO UInt32 := do
  let [source, explicitWeights, literalSuffix, bytes, count] := args | return 2
  let [some b, some n] := [bytes, count].map String.toNat? | return 2
  let input := (← IO.FS.readBinFile source).data.toList
  match read b n input with
  | .error reason =>
    IO.println (reprStr reason)
    return 3
  | .ok result =>
    IO.FS.writeBinFile explicitWeights ⟨result.weights.toArray.map Nat.toUInt8⟩
    IO.FS.writeBinFile literalSuffix ⟨result.rest.toArray⟩
    IO.println result.consumed
    return 0
