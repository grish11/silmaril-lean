module

import Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Defs
meta import Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Defs

open Silmaril.Formats.Compression.Zstd.Huffman
open FourStream

private def treeLimits : DirectWeights.Limits := ⟨65, 129, 11⟩

public def main (args : List String) : IO UInt32 := do
  let [source, destination, mode, declared, count, input, output] := args | return 2
  let [some d, some n, some i, some o] := [declared, count, input, output].map String.toNat? | return 2
  let bytes := (← IO.FS.readBinFile source).data.toList
  let limits : Limits := ⟨i, o⟩
  if mode = "split" then
    match split limits d n bytes with
    | .error reason =>
      IO.println (reprStr reason)
      return 3
    | .ok parts =>
      for chunk in parts.chunks do
        IO.println s!"{chunk.bytes.length} {chunk.symbols}"
      return 0
  else if mode = "decode" then
    let .ok parsed := DirectWeights.read treeLimits bytes | return 4
    match decode limits treeLimits parsed.tree d n parsed.rest with
    | .error reason =>
      IO.println (reprStr reason)
      return 3
    | .ok decoded =>
      IO.FS.writeBinFile destination ⟨decoded.toArray⟩
      return 0
  else return 2
