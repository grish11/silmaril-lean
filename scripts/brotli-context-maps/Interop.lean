module

import Lean
import Silmaril.Formats.Compression.Brotli.ContextMap.Defs
import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs
meta import Silmaril.Formats.Compression.Brotli.ContextMap.Defs
meta import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.ContextMap

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def limited : Error → Bool
  | .count .bitLimit | .bitLimit
  | .description .bitLimit | .description (.simple .bitLimit)
  | .description (.secondary .bitLimit) | .description (.main (.lengths .bitLimit))
  | .description (.main (.lengths (.symbol .bitLimit))) => true
  | _ => false

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

public def main (args : List String) : IO UInt32 := do
  let [file, startControlArg, requests] := args | return 2
  let some startControl := startControlArg.toNat? | return 2
  let source := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  let some (_, beginning) := source.readBits startControl | return 2
  let (header, afterHeader) ← requireIO (Silmaril.Formats.Compression.Brotli.ContextHeader.read 12000 beginning)
  let mut afterLiteral : Option LSBReader := none
  for line in (← IO.FS.readFile requests).splitOn "\n" do
    if line.isEmpty then continue
    let [kindArg, startArg, stopArg, typesArg] := line.splitOn " " | return 2
    let (some start, some stop, some types) := (startArg.toNat?, stopArg.toNat?, typesArg.toNat?) | return 2
    let some (_, before) := source.readBits start | return 2
    let some (_, expected) := source.readBits stop | return 2
    let kind := if kindArg == "literal" then Kind.literal else .distance
    if kind == .literal then
      unless header.controls.literal.typeCount == types && sameCursor afterHeader before do
        throw (IO.userError "literal map does not start at the header boundary")
    else
      unless header.controls.distance.typeCount == types do throw (IO.userError "distance type count")
      if let some cursor := afterLiteral then
        unless sameCursor cursor before do throw (IO.userError "implicit literal map did not reach distance count")
    let size := kind.extent types
    let cap := stop - start
    match read kind types ⟨size, cap - 1⟩ before with
    | .error reason => unless limited reason do throw (IO.userError (reprStr reason))
    | .ok _ => throw (IO.userError "one-bit-short cap accepted")
    let (result, after) ← requireIO (read kind types ⟨size, cap⟩ before)
    unless sameCursor after expected do throw (IO.userError "prefix cursor differs")
    match result with
    | .implicit entries =>
      unless (List.range entries).all (fun i => result.implicitIndex? i == some 0) &&
          (result.implicitIndex? entries).isNone do throw (IO.userError "implicit map index")
      if kind == .literal then afterLiteral := some after
      IO.println (toJson [entries, 1]).compress
    | .coded entries trees rleMax table =>
      IO.println (toJson [entries, trees, rleMax, table.alphabetSize]).compress
  return 0
