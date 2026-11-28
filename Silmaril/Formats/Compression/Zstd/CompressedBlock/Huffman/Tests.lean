module

import Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd
open CompressedBlock (Limits)
open CompressedBlock.Huffman

private def profile : Huffman.TreeDescription.Limits := ⟨128, ⟨256, 11⟩⟩
private def limits : Limits := ⟨64, 32, 32, 4⟩
private def seed : List UInt8 := [0x20, 97, 98, 99, 100, 1, 0x18, 2, 0x10, 0x3f, 3, 0x22]
private def repeatBody : List UInt8 := [0x20, 119, 120, 121, 122, 1, 0xfc, 3, 0x22]

private def first := CompressedBlock.Huffman.decode limits (State.initial profile) seed.length seed

#guard first.map (·.bytes) = .ok [97, 98, 99, 100, 97, 98, 99]
#guard first.map (·.next.block.history.offsets) = .ok ⟨4, 1, 4⟩
#guard (first.bind fun result =>
    CompressedBlock.Huffman.decode limits result.next repeatBody.length repeatBody |>.map (·.bytes)) =
  .ok [119, 120, 121, 122, 119, 120, 121]

private def history : CompressedBlock.State := CompressedBlock.State.initial.advancePlain 8 [0, 1, 2, 3, 4, 5, 6, 7, 8]
private def windowState : State profile := ⟨(State.initial profile).literals, history⟩

#guard (CompressedBlock.Huffman.decode {limits with window := 8} windowState 7 [0, 1, 0x54, 0, 3, 0, 11]).map
    (·.bytes) = .error (.block (.execution .offsetOutsideWindow))

#guard (CompressedBlock.Huffman.decode limits (State.initial profile) 4 [0, 0, 255, 0]).map
    (·.bytes) = .error (.block (.tables (.prefix .trailingEmptySection)))
