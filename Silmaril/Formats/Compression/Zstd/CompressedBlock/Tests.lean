module

import Silmaril.Formats.Compression.Zstd.CompressedBlock.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.CompressedBlock.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd.CompressedBlock

private def limits : Limits := ⟨64, 32, 32, 4⟩

private def seed : List UInt8 := [0x20, 97, 98, 99, 100, 1, 0x18, 2, 0x10, 0x3f, 3, 0x22]
private def first := decode limits State.initial seed.length seed

#guard first.map (·.bytes) = .ok [97, 98, 99, 100, 97, 98, 99]
#guard first.map (·.next.history.offsets) = .ok ⟨4, 1, 4⟩
#guard first.map (·.next.history.recent) = .ok #[97, 98, 99, 100, 97, 98, 99]

private def unsequenced (body : List UInt8) := first.bind fun established =>
  (decode limits established.next body.length body).map fun result =>
    (result.bytes, result.next.tables == established.next.tables, result.next.history.offsets)

#guard unsequenced [0x10, 0xaa, 0xbb, 0] = .ok ([0xaa, 0xbb], true, ⟨4, 1, 4⟩)
#guard unsequenced [0x29, 0xee, 0] = .ok ([0xee, 0xee, 0xee, 0xee, 0xee], true, ⟨4, 1, 4⟩)

private def badMarker : List UInt8 := [0, 1, 0x54, 0, 1, 3, 0]
private def noLiterals : List UInt8 := [0, 1, 0x54, 1, 0, 0, 1]
private def repeated : List UInt8 := [0x20, 119, 120, 121, 122, 1, 0xfc, 3, 0x22]

#guard first.bind (fun state => decode limits state.next badMarker.length badMarker) =
  .error (.sequences .badEndMarker)
#guard first.bind (fun state => decode limits state.next noLiterals.length noLiterals) =
  .error (.execution .literalUnderflow)
#guard (first.bind fun established =>
    match decode limits established.next badMarker.length badMarker with
    | .error (.sequences .badEndMarker) =>
      (decode limits established.next repeated.length repeated).map (·.bytes)
    | _ => .error .sizeMismatch) = .ok [119, 120, 121, 122, 119, 120, 121]

#guard decode limits State.initial 11 seed = .error .sizeMismatch
#guard decode limits State.initial 13 seed = .error .sizeMismatch
#guard decode {limits with inputBytes := 11} State.initial seed.length seed = .error .inputLimit
#guard decode {limits with outputBytes := 3} State.initial seed.length seed = .error (.literals .outputLimit)
#guard decode {limits with outputBytes := 6} State.initial seed.length seed = .error (.execution .outputLimit)
#guard decode {limits with commands := 0} State.initial seed.length seed =
  .error (.tables (.prefix .sequenceLimit))
#guard decode limits State.initial 2 [2, 0] = .error (.literals (.unsupported .huffmanLiterals))
#guard decode limits State.initial 2 [3, 0] = .error (.literals (.unsupported .treelessLiterals))

private def windowState := State.initial.advancePlain 8 [0, 1, 2, 3, 4, 5, 6, 7, 8]
#guard windowState.history.recent = #[1, 2, 3, 4, 5, 6, 7, 8]
#guard decode {limits with window := 8} windowState 7 [0, 1, 0x54, 0, 3, 0, 11] =
  .error (.execution .offsetOutsideWindow)
