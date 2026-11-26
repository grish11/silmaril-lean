module

import Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd
open SequenceTables (Limits Section)
open SequenceTables.Repeat

private def limits : Limits := ⟨32, 1⟩
private def allRepeat : List UInt8 := [1, 0xfc, 0x5a, 1]

#guard resolve limits State.empty [1, 0xc0, 1] = .error (.missingTable .literalLength)
#guard resolve limits State.empty [1, 0x30, 1] = .error (.missingTable .offset)
#guard resolve limits State.empty [1, 0x0c, 1] = .error (.missingTable .matchLength)
#guard (resolve limits State.empty [0]).bind (fun (_, state) => resolve limits state allRepeat) =
  .error (.missingTable .literalLength)
#guard SequenceTables.resolve limits allRepeat = .error (.unsupportedMode .literalLength 3)

private def start := resolve limits State.empty [1, 0x54, 4, 2, 0, 1]

#guard (start.bind fun (_, state) => resolve limits state [0]).map
    (fun (result, state) => (result, state.previous)) =
  .ok (.empty, some ⟨.rle 4, .rle 2, .rle 0⟩)
#guard (start.bind fun (_, state) => resolve limits state [128, 0]).map Prod.snd =
  start.map Prod.snd
#guard (start.bind fun (_, state) => (resolve limits state [0]).bind fun (_, next) =>
    (resolve limits next allRepeat).map Prod.fst) =
  .ok (.coded 1 ⟨.rle 4, .rle 2, .rle 0⟩ [0x5a, 1])

-- Replace offset and match length independently, retaining the literal table.
private def replaced := start.bind fun (_, state) => resolve limits state [1, 0xd4, 3, 1, 1]

#guard replaced.map (fun (_, state) => state.previous) = .ok (some ⟨.rle 4, .rle 3, .rle 1⟩)
#guard (replaced.bind fun (_, state) => (resolve limits state allRepeat).map Prod.fst) =
  .ok (.coded 1 ⟨.rle 4, .rle 3, .rle 1⟩ [0x5a, 1])
#guard (start.bind fun (_, state) => resolve limits state [0, 1]) = .error (.prefix .trailingEmptySection)
#guard (start.bind fun (_, state) => resolve limits state [1, 0xfc]) = .error (.prefix .missingBitstream)
#guard (start.bind fun (_, state) => resolve limits state [1, 0xd4, 3]) =
  .error (.prefix (.missingRleSymbol .matchLength))
#guard (start.bind fun (_, state) => resolve ⟨3, 1⟩ state allRepeat) = .error (.prefix .inputLimit)
#guard (start.bind fun (_, state) => resolve ⟨4, 0⟩ state allRepeat) = .error (.prefix .sequenceLimit)
