module

import Lean
import Silmaril.Formats.Compression.Brotli.Huffman.Description.Defs
meta import Silmaril.Formats.Compression.Brotli.Huffman.Description.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman.Description

private def requireIO {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

private def isLimit : Error → Bool
  | .bitLimit | .simple .bitLimit | .secondary .bitLimit
  | .main (.lengths .bitLimit) | .main (.lengths (.symbol .bitLimit)) => true
  | _ => false

public def main (args : List String) : IO UInt32 := do
  let [file, requests] := args | return 2
  let source := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  for line in (← IO.FS.readFile requests).splitOn "\n" do
    if line.isEmpty then continue
    let [startArg, stopArg, alphabetArg, singletonArg] := line.splitOn " " | return 2
    let (some start, some stop, some alphabet) :=
      (startArg.toNat?, stopArg.toNat?, alphabetArg.toNat?) | return 2
    let some (_, before) := source.readBits start | return 2
    let width := stop - start
    match read ⟨alphabet, width - 1⟩ alphabet before with
    | .error reason =>
      if !isLimit reason then throw (IO.userError s!"one-bit-short cap gave {reprStr reason}")
    | .ok _ => throw (IO.userError "accepted a one-bit-short description")
    let (table, after) ← requireIO (read ⟨alphabet, width⟩ alphabet before)
    let some (_, expected) := source.readBits stop | return 2
    if !sameCursor after expected || table.alphabetSize ≠ alphabet then
      throw (IO.userError "description cursor or alphabet mismatch")
    match table with
    | .singleton _ ordinal _ =>
      if singletonArg.toNat? ≠ some ordinal then throw (IO.userError "unexpected singleton")
      let reader : LSBReader := ⟨0, 0, [], 123⟩
      let some (symbol, next) := table.readSymbol reader | throw (IO.userError "singleton read failed")
      if symbol ≠ ordinal || !sameCursor reader next then throw (IO.userError "singleton consumed bits")
    | .canonical _ =>
      if singletonArg ≠ "-" then throw (IO.userError "expected zero-bit singleton")
    let codes := (List.range alphabet).map fun ordinal =>
      (table.codeFor ordinal).map fun (code, width) => [code, width]
    IO.println (toJson codes).compress
  return 0
