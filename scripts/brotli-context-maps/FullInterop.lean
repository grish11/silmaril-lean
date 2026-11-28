module

import Lean
import Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Defs
import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs
meta import Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Defs
meta import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.ContextMap (Kind)
open Silmaril.Formats.Compression.Brotli.ContextMap.Decode

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def limited : Error → Bool
  | .prefixError (.count .bitLimit) | .bitLimit => true
  | _ => false

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

public def main (args : List String) : IO UInt32 := do
  let [file, startControlArg, requests] := args | return 2
  let some startControl := startControlArg.toNat? | return 2
  let source := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  let some (_, beginning) := source.readBits startControl | return 2
  let (header, afterHeader) ← requireIO (ContextHeader.read 12000 beginning)
  let mut cursor := afterHeader
  for line in (← IO.FS.readFile requests).splitOn "\n" do
    if line.isEmpty then continue
    let [kindArg, startArg, endArg, typesArg, workArg] := line.splitOn " " | return 2
    let (some start, some stop, some types, some work) :=
      (startArg.toNat?, endArg.toNat?, typesArg.toNat?, workArg.toNat?) | return 2
    let some (_, expected) := source.readBits stop | return 2
    let (kind, typeCount) := if kindArg == "literal"
      then (Kind.literal, header.controls.literal.typeCount)
      else (.distance, header.controls.distance.typeCount)
    unless types == typeCount && cursor.totalRead == start do
      throw (IO.userError "map does not start at the previous Lean cursor")
    let entries := kind.extent types
    let cap := stop - start
    match read kind types ⟨entries, work, cap - 1⟩ cursor with
    | .error reason => unless limited reason do throw (IO.userError (reprStr reason))
    | .ok _ => throw (IO.userError "one-bit-short cap accepted")
    if work > 0 then
      match read kind types ⟨entries, work - 1, cap⟩ cursor with
      | .error .symbolLimit => pure ()
      | other => throw (IO.userError
          s!"one-symbol-short cap returned {reprStr (other.toOption.map fun (map, _) => map)}")
    let (result, after) ← requireIO (read kind types ⟨entries, work, cap⟩ cursor)
    unless sameCursor after expected do throw (IO.userError "full map cursor differs")
    cursor := after
    IO.println (toJson (result.treeCount :: result.indices)).compress
  return 0
