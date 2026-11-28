module

import Silmaril.Formats.Arrow.MixedFlat.File.Window.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.File.Window.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Window.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.File.Window.Fixture

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.File.Window MixedFlat.File.Window.Fixture

private def fields : List MixedFlat.Field :=
  [⟨"signed", true, .primitive .int32⟩, ⟨"octets", true, .view .binary⟩]

private def firstInts : Arrow.Column :=
  [some (.int32 (-7)), none, some (.int32 42), some (.int32 (-2147483648))]

private def firstOctets : List (Option (List UInt8)) :=
  [some [], none, some (List.replicate 12 255), some ((List.range 13).map UInt8.ofNat)]

private def lastInts : Arrow.Column := [some (.int32 0), some (.int32 2147483647)]

private def lastOctets : List (Option (List UInt8)) := [some "tail".toUTF8.data.toList, none]

private def observes (observed : MixedFlat.Observed) (ints : Arrow.Column)
    (octets : List (Option (List UInt8))) : Bool :=
  match observed.columns with
  | [(integer, .primitive decoded), (view, .binaryView bytes)] =>
    decide (observed.rowCount = ints.length ∧ [integer, view] = fields ∧
      decoded = ints ∧ bytes.map (Option.map KBytes.toList) = octets)
  | _ => false

private def reads (source : KBytes) : Bool := Id.run do
  let .ok index := readIndex {} source start stop | return false
  let .ok (some last) := index.readAt {} 2 | return false
  let .ok (some first) := index.readAt {} 0 | return false
  let .ok (some empty) := index.readAt {} 1 | return false
  let .ok none := index.readAt {} 3 | return false
  return decide (index.footerStart = footerStart ∧ index.span.length = 264 ∧
      index.footer.fields = fields ∧
      index.footer.blocks = [⟨256, 232, 112⟩, ⟨600, 192, 0⟩, ⟨792, 232, 48⟩]) &&
    observes first firstInts firstOctets && observes empty [] [] && observes last lastInts lastOctets

#guard reads carrier
#guard [64, 72, 256, 488, 600, 792, 1072, 1080, 1354].all fun split =>
  reads (carrier.slice 0 split ++ carrier.slice split (carrier.len - split))

private def patch (input : KBytes) (offset width value : Nat) : KBytes :=
  input.slice 0 offset ++ .leaf width value ++ input.slice (offset + width) (input.len - (offset + width))

private def rejects (source : KBytes) (expected : MixedFlat.File.Window.Error)
    (begin : Nat := start) (finish : Nat := stop) (limits : Arrow.Limits := {}) : Bool :=
  match readIndex limits source begin finish with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard rejects carrier (.window (.malformed .truncated)) stop start
#guard rejects carrier (.window (.malformed .truncated)) start (carrier.len + 1)
#guard rejects carrier (.window (.malformed .alignment)) (start + 1) stop
#guard rejects (.node carrier.len .empty .empty) (.window (.malformed .source))
#guard rejects carrier (.file (.footer (.malformed .source))) start (stop - 1)
#guard rejects (patch carrier footerFieldName 1 84) (.file .schemaMismatch)
#guard rejects (patch carrier (footerStart - 8) 4 0) (.file (.eos (.malformed .continuation)))
#guard rejects (patch carrier (footerStart - 4) 4 8) (.file (.eos (.malformed .trailingBytes)))
#guard rejects (patch carrier firstBlockSlot 8 0) (.file .blockLayout)
#guard rejects (patch carrier firstBlockSlot 8 (256 - start)) (.file .blockLayout)
#guard rejects carrier (.file (.footer (.limit .batches))) (limits := { batches := 2 })

-- This complete extra frame is readable on the carrier at byte 1376,
-- wholly beyond the declared file window.
private def extended : KBytes :=
  carrier ++ KBytes.leaf (1376 - carrier.len) 0 ++ carrier.slice 792 280

#guard Id.run do
  let .ok outside := MixedFlat.File.readRecord {} extended fields ⟨1376, 232, 48⟩ | return false
  return observes outside lastInts lastOctets && reads extended &&
    rejects (patch extended (firstBlockSlot + 48) 8 1376) (.file .blockLayout) &&
    rejects (patch extended (firstBlockSlot + 64) 8 376) (.file .blockLayout)

#guard Id.run do
  let damaged := patch extended (start + 12) 4 1280
  let .ok (.metadata 1280) := readEnvelope {} damaged (start + 8) | return false
  return rejects damaged (.file (.schema (.malformed .truncated)))

-- A selected frame's prefix claims extra available bytes past the window.
-- The indexed metadata length is still bounded and selection fails closed.
#guard Id.run do
  let damaged := patch extended 796 4 576
  let .ok (.metadata 576) := readEnvelope {} damaged 792 | return false
  let .ok index := readIndex {} damaged start stop | return false
  let .error (.file (.batch 2 .metadataLength)) := index.readAt {} 2 | return false
  let .ok (some first) := index.readAt {} 0 | return false
  return observes first firstInts firstOctets

#guard Id.run do
  let .ok index := readIndex {} (patch carrier 572 1 255) start stop | return false
  let .error (.file (.batch 0 (.decode (.field 1 (.view (.slot 3 .prefixMismatch)))))) :=
    index.readAt {} 0 | return false
  let .ok (some last) := index.readAt {} 2 | return false
  let .ok (some empty) := index.readAt {} 1 | return false
  return observes empty [] [] && observes last lastInts lastOctets

#guard Id.run do
  let .ok index := readIndex {} (patch carrier 1040 4 (2^31)) start stop | return false
  let .error (.file (.batch 2 (.decode (.field 1 (.view (.slot 0 .negativeLength)))))) :=
    index.readAt {} 2 | return false
  let .ok (some first) := index.readAt {} 0 | return false
  let .ok (some empty) := index.readAt {} 1 | return false
  return observes empty [] [] && observes first firstInts firstOctets

#guard Id.run do
  let .error (.footer (.malformed .source)) := MixedFlat.File.readIndex {} carrier | return false
  let .error .blockLayout := MixedFlat.File.readIndex {} (carrier.slice start (stop - start)) |
    return false
  return true
