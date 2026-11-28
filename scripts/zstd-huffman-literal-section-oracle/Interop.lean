module

import Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Defs
meta import Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Defs

open Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection

public def main (args : List String) : IO UInt32 := do
  let [source, literals, suffix, input, output] := args | return 2
  let [some i, some o] := [input, output].map String.toNat? | return 2
  let bytes := (← IO.FS.readBinFile source).data.toList
  match read ⟨i, o, ⟨128, ⟨256, 11⟩⟩⟩ bytes with
  | .error reason =>
    IO.println (reprStr reason)
    return 3
  | .ok result =>
    IO.FS.writeBinFile literals ⟨result.literals.toArray⟩
    IO.FS.writeBinFile suffix ⟨result.rest.toArray⟩
    let header := result.header
    IO.println s!"{header.format.code} {header.compressed} {header.regenerated} {result.consumed}"
    return 0
