module

import Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Defs
meta import Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Defs

open Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman

public def main (args : List String) : IO UInt32 := do
  let [path, out, inputCap, outputCap, windowCap, commands] := args | return 2
  let (some i, some o, some w, some n) :=
    (inputCap.toNat?, outputCap.toNat?, windowCap.toNat?, commands.toNat?) | return 2
  let input ← IO.FS.readBinFile path
  match decode ⟨⟨i, o, w⟩, n, ⟨128, ⟨256, 11⟩⟩⟩ input.data.toList with
  | .ok bytes =>
    IO.FS.writeBinFile out ⟨bytes.toArray⟩
    return 0
  | .error reason =>
    IO.println (reprStr reason)
    return 3
