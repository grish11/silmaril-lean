module

import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Defs
meta import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Defs

open Silmaril.Formats.Compression.Zstd.Huffman

public def main (args : List String) : IO UInt32 := do
  let [source, symbols, depth] := args | return 2
  let [some s, some d] := [symbols, depth].map String.toNat? | return 2
  let transmitted := (← IO.FS.readBinFile source).data.toList.map UInt8.toNat
  let limits : Weights.Limits := ⟨s, d⟩
  match Weights.complete limits transmitted with
  | .error reason =>
    IO.println (reprStr reason)
    return 3
  | .ok tree =>
    let .ok table := SingleStream.buildGeneral limits tree | return 4
    let expected := tree.weights.zipIdx.filterMap fun (weight, symbol) =>
      if weight = 0 then none else some symbol
    let placed := (table.entries.map SingleStream.Entry.symbol).mergeSort (· ≤ ·)
    if placed != expected then return 4
    IO.println s!"{tree.depth} {tree.weights.length}"
    IO.println (String.intercalate " " (tree.weights.map toString))
    return 0
