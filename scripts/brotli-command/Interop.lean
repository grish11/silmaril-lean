module

import Lean
import Silmaril.Formats.Compression.Brotli.Command.Defs
meta import Silmaril.Formats.Compression.Brotli.Command.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Command

private def modeCode : DistanceMode → Nat
  | .implicitZero => 0
  | .explicit => 1

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

private def capError : Command.Error → Bool
  | .symbol .bitLimit | .bitLimit _ => true
  | _ => false

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def checkCommands (file requests : String) (start payload types : Nat) : IO UInt32 := do
  let source := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  let some (_, before) := source.readBits start | return 2
  let (header, first) ← requireIO (CompressedHeader.read ⟨17408, 768, payload - start⟩ before)
  unless first.totalRead == payload && header.initial.controls.insertCopy.typeCount == types do
    throw (IO.userError "checked command group or payload boundary differs")
  if types > 1 then
    match Command.readSingle header 63 first with
    | .error .commandBlockTypes => pure ()
    | _ => throw (IO.userError "single-type entry point accepted a multi-type header")
  let mut cursor := first
  for line in (← IO.FS.readFile requests).splitOn "\n" do
    if line.isEmpty then continue
    let [typeArg, beginArg, endArg] := line.splitOn " " | return 2
    let (some type, some beginBit, some endBit) := (typeArg.toNat?, beginArg.toNat?, endArg.toNat?)
      | return 2
    unless cursor.totalRead ≤ beginBit && beginBit ≤ endBit do
      throw (IO.userError "native command offsets out of order")
    let some (_, atCommand) := cursor.readBits (beginBit - cursor.totalRead) | return 2
    let some (_, expected) := atCommand.readBits (endBit - beginBit) | return 2
    let some table := header.insertCopyTrees[type]? | return 2
    let decode := if types == 1 then Command.readSingle header else Command.read table
    let cap := endBit - beginBit
    if cap > 0 then
      match decode (cap - 1) atCommand with
      | .error reason => unless capError reason do throw (IO.userError (reprStr reason))
      | .ok _ => throw (IO.userError "one-bit-short command accepted")
    let (command, after) ← requireIO (decode cap atCommand)
    unless sameCursor after expected do
      throw (IO.userError s!"command cursor differs at bit {beginBit}")
    IO.println (toJson [type, command.symbol.val, command.insertLength, command.copyLength,
      modeCode command.distance, beginBit, after.totalRead]).compress
    cursor := after
  return 0

public def main (args : List String) : IO UInt32 := do
  if args == ["--lut"] then
    for symbol in List.finRange 704 do
      let fields := spec symbol
      IO.println (toJson [symbol.val, fields.insert.base, fields.insert.extraBits,
        fields.copy.base, fields.copy.extraBits, modeCode fields.distance]).compress
    return 0
  else
    let [file, requests, startArg, payloadArg, typeArg] := args | return 2
    let (some start, some payload, some types) := (startArg.toNat?, payloadArg.toNat?, typeArg.toNat?)
      | return 2
    checkCommands file requests start payload types
