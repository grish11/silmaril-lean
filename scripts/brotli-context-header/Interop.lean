module

import Lean
import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs
meta import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.ContextHeader

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

public def main (args : List String) : IO UInt32 := do
  let [file, startArg, controlArg, stopArg] := args | return 2
  let (some start, some controlEnd, some stop) :=
    (startArg.toNat?, controlArg.toNat?, stopArg.toNat?) | return 2
  let source := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  let some (_, before) := source.readBits start | return 2
  let some (_, controlCursor) := source.readBits controlEnd | return 2
  let some (_, expected) := source.readBits stop | return 2
  let cap := stop - start
  let (header, after) ← requireIO (read cap before)
  unless sameCursor after expected do throw (IO.userError "combined cursor differs")
  let (controls, afterControls) ← requireIO
    (Silmaril.Formats.Compression.Brotli.BlockTypes.read (controlEnd - start) before)
  unless sameCursor afterControls controlCursor do throw (IO.userError "control boundary differs")
  let (fields, tail) ← requireIO
    (readAfter controls.literal.typeCount (stop - controlEnd) controlCursor)
  unless header.fields == fields && sameCursor tail after do throw (IO.userError "field reader differs")
  match read (cap - 1) before with
  | .error .bitLimit => pure ()
  | .error reason => throw (IO.userError s!"wrong one-bit-short error: {reprStr reason}")
  | .ok _ => throw (IO.userError "one-bit-short cap accepted")
  IO.println (toJson [fields.postfixBits.val, fields.direct, fields.distanceAlphabet]).compress
  IO.println (toJson (fields.modes.map Mode.code)).compress
  return 0
