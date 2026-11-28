module

import Lean
import Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Defs
meta import Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman

private def requireIO {ε α : Type} [Repr ε] : Except ε α → IO α
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

public def main (args : List String) : IO UInt32 := do
  let [file, requests] := args | return 2
  let source := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  for line in (← IO.FS.readFile requests).splitOn "\n" do
    if line.isEmpty then continue
    let [prefixArg, startArg, stopArg, alphabetArg] := line.splitOn " " | return 2
    let (some begin, some start, some stop, some alphabet) :=
      (prefixArg.toNat?, startArg.toNat?, stopArg.toNat?, alphabetArg.toNat?) | return 2
    let some (_, before) := source.readBits begin | return 2
    let (table, reader) ← requireIO (Brotli.Huffman.CodeLengths.read (start - begin) before)
    let some (_, expectedStart) := source.readBits start | return 2
    if !sameCursor reader expectedStart then throw (IO.userError "secondary cursor mismatch")
    let budget := stop - start
    if budget > 0 then
      match MainLengths.read ⟨alphabet, budget - 1⟩ alphabet table reader with
      | .error .bitLimit | .error (.symbol .bitLimit) => pure ()
      | .error error => throw (IO.userError s!"one-bit-short cap gave {reprStr error}")
      | .ok _ => throw (IO.userError "one-bit-short cap was accepted")
    let (lengths, after) ← requireIO (MainLengths.read ⟨alphabet, budget⟩ alphabet table reader)
    let some (_, expectedStop) := source.readBits stop | return 2
    if !sameCursor after expectedStop then throw (IO.userError "main lengths cursor mismatch")
    IO.println (toJson lengths).compress
  return 0
