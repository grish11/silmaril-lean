module

import Silmaril.Formats.Compression.Brotli.Literal.Thms
meta import Silmaril.Formats.Compression.Brotli.Literal.Defs
meta import Silmaril.Formats.Compression.Checksum.CRC32

namespace Silmaril.Formats.Compression.Brotli.Literal

open Silmaril.Formats.Compression
open ContextHeader (Mode)
open ContextMap.Decode (Map)
open Huffman.Description (Table)

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 5⟩

private def header (mode : Mode) (map : Map) (trees : List Table) : CompressedHeader.Header :=
  ⟨⟨⟨.single, .single, .single⟩, ⟨0, 0, [mode]⟩⟩, map, .implicit 4, trees, [], []⟩

private def single (symbol : Fin 256) : Table := .singleton 256 symbol.val symbol.isLt

private def alternating : CompressedHeader.Header :=
  header .lsb6 (.coded 2 ([0, 1] ++ List.replicate 62 0)) [single 1, single 2]

private def insert3 : Command.Value := Command.value 152 0 0
private def prior : State := ⟨4, ⟨1, 99⟩⟩

private def observed (result : Except Error (Result × LSBReader)) :
    Option (Result × Nat × Option Bool) := do
  let (inserted, after) ← result.toOption
  pure (inserted, after.totalRead, after.readBit |>.map Prod.fst)

private def errorOf (result : Except Error (Result × LSBReader)) : Option Error :=
  match result with
  | .error reason => some reason
  | .ok _ => none

private def pair : Option Table := do
  let description := natBits 1 2 ++ natBits 1 2 ++ natBits 65 8 ++ natBits 66 8
  let (table, _) ← (Huffman.Description.read ⟨256, 20⟩ 256 (cursor description)).toOption
  pure table

#guard crc32List (utf8MostRecent.toList.map (·.val)) == 0x8e91efb7
#guard crc32List (utf8SecondRecent.toList.map (·.val)) == 0xd01a32f4
#guard crc32List (signedClasses.toList.map (·.val)) == 0x0dd7a0d6
#guard (contextId .lsb6 ⟨193, 255⟩).val = 1
#guard (contextId .msb6 ⟨193, 255⟩).val = 48
#guard (contextId .utf8 ⟨65, 97⟩).val = 51
#guard (contextId .signed ⟨255, 240⟩).val = 62

#guard observed (read alternating insert3 7 ⟨7, 0⟩ prior (cursor [true])) =
  some (⟨[2, 1, 2], ⟨7, ⟨2, 1⟩⟩, .endOfMetaBlock⟩, 5, some true)
#guard observed (read alternating insert3 8 ⟨7, 0⟩ prior (cursor [])) =
  some (⟨[2, 1, 2], ⟨7, ⟨2, 1⟩⟩, .copyPending⟩, 5, none)
#guard observed (read alternating (Command.value 128 0 0) 8 ⟨4, 0⟩ prior (cursor [false])) =
  some (⟨[], prior, .copyPending⟩, 5, some false)
#guard (pair.bind fun tree =>
    observed (read (header .msb6 (.implicit 64) [tree]) insert3 3 ⟨3, 3⟩ State.start
      (cursor [false, true, true, false]))) =
  some (⟨[65, 66, 66], ⟨3, ⟨66, 66⟩⟩, .endOfMetaBlock⟩, 8, some false)

#guard (pair.bind fun tree => errorOf (read (header .msb6 (.implicit 64) [tree])
    insert3 3 ⟨3, 2⟩ State.start (cursor [false, true, true]))) = some (.symbol .bitLimit)
#guard (pair.bind fun tree => errorOf (read (header .msb6 (.implicit 64) [tree])
    insert3 3 ⟨3, 3⟩ State.start (cursor [false, true]))) = some (.symbol .truncated)
#guard errorOf (read alternating insert3 7 ⟨6, 0⟩ prior (cursor [])) = some .outputLimit
#guard errorOf (read alternating insert3 6 ⟨7, 0⟩ prior (cursor [])) = some .metaBlockExtent
#guard errorOf (read alternating (Command.value 128 0 0) 4 ⟨8, 0⟩ prior (cursor [])) =
  some .metaBlockExtent
#guard errorOf (read (header .lsb6 (.implicit 63) [single 0]) insert3 3 ⟨3, 0⟩ State.start
    (cursor [])) = some .mapExtent
#guard errorOf (read (header .lsb6 (.implicit 64) []) insert3 3 ⟨3, 0⟩ State.start (cursor [])) =
  some .treeGroup

#guard (
  let initial := alternating.initial
  let controls := { initial.controls with literal := .multiple 2 (single 1) (single 2) 4 }
  let multi := { alternating with initial := { initial with controls := controls } }
  errorOf (read multi insert3 7 ⟨7, 0⟩ prior (cursor []))) = some .literalBlockTypes
#guard (
  let initial := alternating.initial
  let malformed := { alternating with initial := { initial with fields := { initial.fields with modes := [] } } }
  errorOf (read malformed insert3 7 ⟨7, 0⟩ prior (cursor []))) = some .modes

end Silmaril.Formats.Compression.Brotli.Literal
