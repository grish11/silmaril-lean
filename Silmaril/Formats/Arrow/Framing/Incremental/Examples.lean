module

import Silmaril.Formats.Arrow.Framing.Incremental.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Formats.Arrow.Framing.Incremental.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open Arrow.Framing.Incremental Arrow.MixedFlat.Stream.Fixture

private def pump (limits : Limits) :
    Nat → State → KBytes → Except Failure (State × List Frame)
  | 0, state, _ => .error ⟨state.part, state.position, .malformed .source⟩
  | fuel + 1, state, bytes => do
    match ← feed limits state bytes with
    | .wait state => return (state, [])
    | .advance state rest => pump limits fuel state rest
    | .frame value state rest =>
      let (state, following) ← pump limits fuel state rest
      return (state, value :: following)

private def collect (limits : Limits) : State → List KBytes → Except Failure (Nat × List Frame)
  | state, [] => return (← finish state, [])
  | state, chunk :: chunks => do
    let (state, frames) ← pump limits 32 state chunk
    let (last, following) ← collect limits state chunks
    return (last, frames ++ following)

private def range (frame : Frame) : Nat × Nat × Nat :=
  (frame.offset, frame.metadata.len, frame.body.len)

private def matchesCarrier (input : KBytes) (frame : Frame) : Bool := Id.run do
  let .ok (.metadata size) := readEnvelope {} input frame.offset | return false
  let header := input.slice (frame.offset + 8) size
  let .ok bodyLength := frameBodyLength {} header | return false
  let .ok body := readBody {} input (frame.offset + 8 + size) bodyLength | return false
  return decide (frame.metadata.len = size ∧ frame.metadata.toList = header.toList ∧
    frame.body.len = bodyLength ∧ frame.body.toList = body.toList)

private def agrees (input : KBytes) (ranges : List (Nat × Nat × Nat))
    (chunks : List KBytes) (origin : Nat := 0) : Bool := Id.run do
  let .ok (last, frames) := collect {} (start origin) chunks | return false
  let .ok .eos := readEnvelope {} input (last - 8) | return false
  return decide (last = input.len ∧ frames.map range = ranges) && frames.all (matchesCarrier input)

private def splitAt (input : KBytes) (cut : Nat) : List KBytes :=
  [input.slice 0 cut, .empty, input.slice cut (input.len - cut)]

private def recordRanges : List (Nat × Nat × Nat) := (0, multiSchemaSize, 0) :: multiRanges

-- Exercise both length words, all three phases of successive frames, and EOS.
#guard [0, 1, 3, 4, 5, 7, 8, 22, 255, 256, 257, 262, 264, 353, 639, 640, 641, 800,
    912, 915, 920, 1239, 1247, 1249, 1255, 1256, 1615, 1617, 1700, 1743, 1744, 1745,
    1747, 1748, 1751, 1752].all fun cut => agrees multi recordRanges (splitAt multi cut)

#guard agrees multi recordRanges ((List.range multi.len).map fun i => multi.slice i 1)
#guard (List.range (schemaOnly.len + 1)).all fun cut =>
  agrees schemaOnly [(0, multiSchemaSize, 0)] (splitAt schemaOnly cut)

#guard agrees zeroColumns [(0, 48, 0), (56, 72, 0), (136, 64, 0)]
  ((List.range zeroColumns.len).map fun i => zeroColumns.slice i 1)

#guard agrees ((.leaf 16 7 : KBytes) ++ schemaOnly) [(16, multiSchemaSize, 0)]
  (splitAt schemaOnly 5) 16

private def rejects (chunks : List KBytes) (expected : Failure) (limits : Limits := {}) : Bool :=
  match collect limits (start 0) chunks with
  | .error error => decide (error = expected)
  | .ok _ => false

#guard rejects [lateTruncated] ⟨.body, 1616, .malformed .truncated⟩
#guard rejects (splitAt lateTruncated 1619) ⟨.body, 1616, .malformed .truncated⟩
#guard rejects [multi.slice 0 multiEos] ⟨.prefix, multiEos, .malformed .truncated⟩
#guard rejects [multi.slice 0 (multiEos + 6)] ⟨.prefix, multiEos, .malformed .truncated⟩
#guard rejects [multi ++ .leaf 1 0] ⟨.tail, multi.len, .malformed .trailingBytes⟩
#guard rejects [multi, .empty, .leaf 1 0] ⟨.tail, multi.len, .malformed .trailingBytes⟩
#guard rejects [multi.slice 0 11] ⟨.metadata, 0, .malformed .truncated⟩
#guard rejects [multi.slice 0 8] ⟨.prefix, 0, .limit .metadataBytes⟩ { metadataBytes := 200 }
#guard rejects [multi.slice 0 640] ⟨.metadata, 256, .limit .bodyBytes⟩ { bodyBytes := 100 }

#guard Id.run do
  let .ok (.wait pending) := feed {} (start 0) (multi.slice 0 5) | return false
  let .error ⟨.prefix, 0, .malformed .truncated⟩ := finish pending | return false
  return pending.position == 5
