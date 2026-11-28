module

import Lean
import Silmaril.Formats.Compression.Brotli.CompressedHeader.Defs
meta import Silmaril.Formats.Compression.Brotli.CompressedHeader.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.CompressedHeader

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

private def showTable (table : Huffman.Description.Table) : Json :=
  let codes := (List.range table.alphabetSize).filterMap fun symbol =>
    (table.codeFor symbol).map fun (code, width) => [symbol, code, width]
  Json.arr #[toJson table.alphabetSize, toJson codes]

private def showControl : BlockTypes.Control → Json
  | .single => Json.arr #[toJson (1 : Nat)]
  | .multiple types typeTable countTable initial =>
    Json.arr #[toJson types, toJson initial, showTable typeTable, showTable countTable]

private def showMap (map : ContextMap.Decode.Map) : Json :=
  toJson (map.treeCount :: map.indices)

private def showHeader (header : Header) (endBit : Nat) : Json :=
  let controls := header.initial.controls
  let fields := header.initial.fields
  Json.mkObj [
    ("controls", toJson ([controls.literal, controls.insertCopy, controls.distance].map showControl)),
    ("distance", toJson [fields.postfixBits.val, fields.direct]),
    ("modes", toJson (fields.modes.map ContextHeader.Mode.code)),
    ("maps", toJson ([header.literalMap, header.distanceMap].map showMap)),
    ("groups", toJson ([header.literalTrees, header.insertCopyTrees, header.distanceTrees].map (·.map showTable))),
    ("payload", toJson endBit)]

private def limited : Huffman.Description.Error → Bool
  | .bitLimit | .simple .bitLimit | .secondary .bitLimit
  | .main (.lengths .bitLimit) | .main (.lengths (.symbol .bitLimit)) => true
  | _ => false

public def main (args : List String) : IO UInt32 := do
  let [file, startArg, endArg, entriesArg, treesArg, ordinalArg] := args | return 2
  let (some start, some stop, some entries, some trees, some ordinal) :=
    (startArg.toNat?, endArg.toNat?, entriesArg.toNat?, treesArg.toNat?, ordinalArg.toNat?) | return 2
  let source := LSBReader.ofByteArray (← IO.FS.readBinFile file)
  let some (_, before) := source.readBits start | return 2
  let some (_, expected) := source.readBits stop | return 2
  let cap := stop - start
  match read ⟨entries, trees, cap - 1⟩ before with
  | .error (.tree .distance index reason) =>
    unless index == ordinal && limited reason do
      throw (IO.userError s!"one-bit-short bound returned {index}: {reprStr reason}")
  | .error reason => throw (IO.userError s!"one-bit-short bound returned {reprStr reason}")
  | .ok _ => throw (IO.userError "one-bit-short bound accepted")
  match read ⟨entries - 1, trees, cap⟩ before with
  | .error .mapEntryLimit => pure ()
  | _ => throw (IO.userError "wrong outcome for one-entry-short cap")
  match read ⟨entries, trees - 1, cap⟩ before with
  | .error .treeLimit => pure ()
  | _ => throw (IO.userError "wrong outcome for one-tree-short cap")
  match read ⟨entries, trees, cap⟩ before with
  | .error reason => throw (IO.userError (reprStr reason))
  | .ok (header, after) =>
    unless sameCursor after expected do throw (IO.userError "payload cursor differs")
    IO.println (showHeader header after.totalRead).compress
    return 0
