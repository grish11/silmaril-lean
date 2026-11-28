module

import Lean
import Silmaril.Formats.Compression.Brotli.BlockTypes.Defs
meta import Silmaril.Formats.Compression.Brotli.BlockTypes.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.BlockTypes

private def summary (control : Control) : Json :=
  match control with
  | .single => toJson [1]
  | .multiple types typeTable countTable initial =>
    toJson [types, initial, typeTable.alphabetSize, countTable.alphabetSize]

private def limitError : Error → Bool
  | .bitLimit | .description .bitLimit | .description (.simple .bitLimit)
  | .description (.secondary .bitLimit) | .description (.main (.lengths .bitLimit))
  | .description (.main (.lengths (.symbol .bitLimit))) => true
  | _ => false

public def main (args : List String) : IO UInt32 := do
  let [file, startArg, stopArg] := args | return 2
  let (some start, some stop) := (startArg.toNat?, stopArg.toNat?) | return 2
  let origin := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  let some (_, before) := origin.readBits start | return 2
  let some (_, expected) := origin.readBits stop | return 2
  let cap := stop - start
  match read (cap - 1) before with
  | .error reason => unless limitError reason do throw (IO.userError (reprStr reason))
  | .ok _ => throw (IO.userError "one-bit-short cap accepted")
  let (controls, after) ← match read cap before with
    | .ok result => pure result
    | .error reason => throw (IO.userError (reprStr reason))
  unless after.totalRead == expected.totalRead && after.count == expected.count &&
      after.buffer == expected.buffer && after.input == expected.input do
    throw (IO.userError "control boundary or suffix differs")
  let initial : Internal.Cursor := ⟨before, cap⟩
  let .ok (_, first) := Internal.readControl initial | return 2
  let .ok (_, second) := Internal.readControl first | return 2
  let .ok (_, third) := Internal.readControl second | return 2
  let stops := [first.reader.totalRead, second.reader.totalRead, third.reader.totalRead]
  IO.println (Json.arr #[toJson stops, summary controls.literal, summary controls.insertCopy,
    summary controls.distance]).compress
  return 0
