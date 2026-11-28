module

import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Window.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.File.Window.Fixture

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.File.Window MixedFlat.File.Window.Fixture

private def preservesRows (source : KBytes) : Bool := Id.run do
  let .ok index := readIndex {} source start stop | return false
  let some p := index.checkProjection [1, 0, 1] | return false
  let .ok (some reordered) := index.readProjectedAt {} 0 p | return false
  let [(first, .binaryView octets), (second, .primitive ints), (third, .binaryView again)] :=
    reordered.columns | return false
  let some zero := index.checkProjection [] | return false
  let .ok (some four) := index.readProjectedAt {} 0 zero | return false
  let .ok (some empty) := index.readProjectedAt {} 1 zero | return false
  let .ok none := index.readProjectedAt {} 3 zero | return false
  let view : MixedFlat.Field := ⟨"octets", true, .view .binary⟩
  let integer : MixedFlat.Field := ⟨"signed", true, .primitive .int32⟩
  return decide (reordered.rowCount = 4 ∧ [first, second, third] = [view, integer, view] ∧ ints = [some (.int32 (-7)), none, some (.int32 42),
      some (.int32 (-2147483648))] ∧
    octets.map (Option.map KBytes.toList) =
      [some [], none, some (List.replicate 12 255), some ((List.range 13).map UInt8.ofNat)] ∧
    octets.map (Option.map KBytes.toList) = again.map (Option.map KBytes.toList) ∧
    four.rowCount = 4 ∧ four.columns.isEmpty ∧ empty.rowCount = 0 ∧ empty.columns.isEmpty) &&
    (index.checkProjection [1, 2, 0]).isNone

#guard preservesRows carrier

private def corrupt (origin width replacement : Nat) : KBytes :=
  carrier.slice 0 origin ++ .leaf width replacement ++
    carrier.slice (origin + width) (carrier.len - (origin + width))

private def preservesFailure (source : KBytes) (bad good goodRows : Nat)
    (expected : MixedFlat.File.Window.Error) : Bool := Id.run do
  let .ok index := readIndex {} source start stop | return false
  let some p := index.checkProjection [0] | return false
  let .error sourceError := index.readAt {} bad | return false
  let .error projectedError := index.readProjectedAt {} bad p | return false
  let .ok (some intact) := index.readProjectedAt {} good p | return false
  let .ok (some empty) := index.readProjectedAt {} 1 p | return false
  return decide (sourceError = expected ∧ projectedError = expected ∧
    intact.rowCount = goodRows ∧ intact.columns.length = 1 ∧ empty.rowCount = 0)

#guard preservesFailure (corrupt 572 1 255) 0 2 2
  (.file (.batch 0 (.decode (.field 1 (.view (.slot 3 .prefixMismatch))))))
#guard preservesFailure (corrupt 1040 4 (2^31)) 2 0 4
  (.file (.batch 2 (.decode (.field 1 (.view (.slot 0 .negativeLength))))))
