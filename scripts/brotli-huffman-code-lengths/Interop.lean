module

import Lean
import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Defs
meta import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths

private def unroll {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

public def main (args : List String) : IO UInt32 := do
  let [file, requests] := args | return 2
  let startReader := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  for line in (← IO.FS.readFile requests).splitOn "\n" do
    if line.isEmpty then continue
    let [startArg, stopArg] := line.splitOn " " | return 2
    let (some start, some stop) := (startArg.toNat?, stopArg.toNat?) | return 2
    let some (_, before) := startReader.readBits start | return 2
    if start = stop then
      match read 2 before with
      | .error .unsupportedSimple => IO.println "unsupportedSimple"
      | _ => throw (IO.userError "expected unsupportedSimple")
    else
      let budget := stop - start
      match read (budget - 1) before with
      | .error .bitLimit => pure ()
      | _ => throw (IO.userError "expected a one-bit-short limit error")
      let (table, after) ← unroll (read budget before)
      let some (_, expected) := startReader.readBits stop | return 2
      if !sameCursor after expected then
        throw (IO.userError s!"cursor differs from the independent stop {stop}")
      let codes := (List.range 18).map fun symbol =>
        (table.codeFor symbol).map fun (value, width) => [value, width]
      IO.println (toJson (table.lengths.map Length.value, codes)).compress
  return 0
