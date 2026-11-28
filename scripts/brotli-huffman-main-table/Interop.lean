module

import Lean
import Silmaril.Formats.Compression.Brotli.Huffman.MainTable.Defs
meta import Silmaril.Formats.Compression.Brotli.Huffman.MainTable.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman

private def requireIO {ε α : Type} [Repr ε] : Except ε α → IO α
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

private def checkSymbol (table : HuffmanTable) (test : String) : IO Unit := do
  let [symbolArg, widthArg, bitsArg] := test.splitOn ":" | throw (IO.userError "invalid symbol test")
  let (some symbol, some width, some bits) :=
    (symbolArg.toNat?, widthArg.toNat?, bitsArg.toNat?) | throw (IO.userError "invalid symbol arguments")
  let start := LSBReader.ofByteArray ⟨#[bits.toUInt8, (bits >>> 8).toUInt8, (bits >>> 16).toUInt8]⟩
  let some (_, reader) := start.readBits 3 | throw (IO.userError "selected code begins after three sentinel bits")
  let some (actual, after) := table.readSymbolLSB reader |
    throw (IO.userError s!"selected code for {symbol} could not be decoded")
  let some (_, expected) := reader.readBits width | throw (IO.userError "invalid selected width")
  if actual ≠ symbol || !sameCursor after expected then throw (IO.userError s!"selected code at {symbol}")

public def main (args : List String) : IO UInt32 := do
  let [file, requests] := args | return 2
  let source := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  for line in (← IO.FS.readFile requests).splitOn "\n" do
    if line.isEmpty then continue
    let prefixArg :: startArg :: stopArg :: alphabetArg :: tests := line.splitOn " " | return 2
    let (some begin, some start, some stop, some alphabet) :=
      (prefixArg.toNat?, startArg.toNat?, stopArg.toNat?, alphabetArg.toNat?) | return 2
    let some (_, before) := source.readBits begin | return 2
    let (secondary, reader) ← requireIO (Brotli.Huffman.CodeLengths.read (start - begin) before)
    let some (_, expectedStart) := source.readBits start | return 2
    if !sameCursor reader expectedStart then throw (IO.userError "secondary cursor mismatch")
    let (table, after) ← requireIO (MainTable.read ⟨alphabet, stop - start⟩ alphabet secondary reader)
    let some (_, expectedStop) := source.readBits stop | return 2
    if !sameCursor after expectedStop then throw (IO.userError "installed table cursor mismatch")
    if table.decoder.alphabetSize ≠ alphabet || table.decoder.maxBits ≠ 15 then
      throw (IO.userError "installed table dimensions")
    for test in tests do checkSymbol table.decoder test
    let codes := (List.range alphabet).map fun ordinal =>
      (table.decoder.encodeSymbol ordinal).map fun (code, width) => [code, width]
    let entries := table.decoder.entries.map fun entry => [entry.symbol, entry.length]
    IO.println (Json.arr #[toJson table.lengths, toJson entries, toJson codes]).compress
  return 0
