module

import Silmaril.Containers.Cas.Blake3Wire.Thms
meta import Silmaril.Formats.Blake3Cas.Thms
meta import Silmaril.Formats.Iroh.Vectors

open Silmaril.Formats
open Silmaril.Formats.Blake3Cas

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def zeros (count : Nat) : Bao.Bytes := List.replicate count 0

private def relength (size : Nat) (wire : Bao.Bytes) : Bao.Bytes := Bao.putLE64 size ++ wire.drop 8

private def visible {size : Nat} {digest : Bao.Bytes} {request : Bao.RangeRequest}
    (range : ExactRange size digest request) : Bao.Bytes := range.coverage.bytes

private def verifiedVisible {size : Nat} {digest : Bao.Bytes} {request : Bao.RangeRequest}
    (range : ExactRange size digest request × EOFProof size digest) : Bao.Bytes := visible range.1

private def position {size : Nat} {digest : Bao.Bytes} (fact : SpanFact size digest) : Nat × Nat :=
  (fact.offset, fact.bytes.length)

private def unhex (input : String) : Bao.Bytes :=
  let digit := fun ch : Char => if ch ≤ '9' then ch.toNat - 48 else ch.toNat - 87
  let rec bytes : List Char → Bao.Bytes
    | first :: second :: tail => UInt8.ofNat (16 * digit first + digit second) :: bytes tail
    | _ => []
  bytes input.toList

set_option maxRecDepth 8192

#eval do
  let (root, combined, outboard, interior, tail) := Iroh.Vectors.baoFixtures
  let size := 2049
  let inside : Bao.RangeRequest := ⟨1024, 1⟩
  let across : Bao.RangeRequest := ⟨1023, 1026⟩
  let check := checkBaoInline? .combined 4096 root
  let some inline := check combined | throw (IO.userError "Bao combined")
  let some detached := checkBaoOutboard? 4096 root outboard (zeros size) |
    throw (IO.userError "Bao outboard")
  require "Bao interleaved/detached schedules differ" (inline.fields == detached.fields)
  require "Bao verified range crossing chunk boundary"
    ((inline.body.verifiedRange? across).map verifiedVisible == some (zeros 1026))
  require "Bao detached verified EOF" detached.body.final.eof.isSome
  require "Bao detached truncated pair" (checkBaoOutboard? 4096 root (outboard.take 135) (zeros size)).isNone
  require "Bao detached substituted data" (checkBaoOutboard? 4096 root outboard (1 :: zeros 2048)).isNone
  require "Bao detached original length" (checkBaoOutboard? 4096 root outboard (zeros 2050)).isNone
  require "Bao truncated body" (check (combined.take 2184)).isNone
  require "Bao trailing bytes" (check (combined ++ [0])).isNone
  require "Bao truncated header" (check (combined.take 7)).isNone
  require "Bao extent cap" (checkBaoInline? .combined 2048 root combined).isNone
  require "Bao substituted data" (check (combined.take 2184 ++ [1])).isNone
  let (header, body) := (combined.take 8, combined.drop 8)
  require "Bao reordered pairs" (check (header ++ (body.drop 64).take 64 ++ body.take 64 ++ body.drop 128)).isNone
  require "Bao reordered CVs" (check (header ++ (body.drop 32).take 32 ++ body.take 32 ++ body.drop 64)).isNone
  let slice := checkBaoInline? (.slice inside) 4096 root
  let some interiorFrame := slice interior | throw (IO.userError "Bao interior slice")
  require "Bao trusted prefix"
    ((interiorFrame.body.trustedRange? size inside).map visible == some [0])
  require "Bao interior does not authenticate EOF" (interiorFrame.body.verifiedRange? inside).isNone
  require "Bao uncovered exact window" (interiorFrame.body.trustedRange? size ⟨1023, 2⟩).isNone
  require "Bao smaller claim with different path" (slice (relength 2048 interior)).isNone
  for claim in [2050, 3072, 3073] do
    let some falsePrefix := slice (relength claim interior) | throw (IO.userError "Bao false-length prefix")
    require "false length cannot become trusted" (falsePrefix.body.trustedRange? size inside).isNone
    require "false length cannot produce EOF" (falsePrefix.body.verifiedRange? inside).isNone
  let checkTail := checkBaoInline? (.slice ⟨2048, 1⟩) 4096 root
  let some right := checkTail tail | throw (IO.userError "Bao right edge")
  require "Bao final chunk proves EOF" right.body.final.eof.isSome
  require "Bao false length matching padding rejected" (checkTail (relength 2050 tail ++ [0])).isNone
  let emptyRoot := unhex "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
  let some empty := checkBaoInline? .combined 0 emptyRoot (zeros 8) | throw (IO.userError "Bao zero root")
  require "Bao zero root proves EOF" empty.body.final.eof.isSome

#eval do
  let (root, full, subdivided, past) := Iroh.Vectors.rawGetFixtures
  let cap := 40000
  let requestHead := 0 :: root
  let fullReq := requestHead ++ [2, 0, 1, 0, 1, 0]
  let partialReq := requestHead ++ [2, 0, 2, 1, 1, 1, 0]
  let edgeReq : Bao.Bytes := requestHead ++ [2, 0, 2, 99, 1, 1, 0]
  let some all := checkIrohRawGet? cap root fullReq full | throw (IO.userError "Iroh all")
  require "Iroh grouped rather than official Bao schedule"
    (all.frame.fields.map List.length == [64, 64, 16384, 16384, 1])
  require "Iroh grouped frame proves EOF" all.frame.body.final.eof.isSome
  let some part := checkIrohRawGet? cap root partialReq subdivided | throw (IO.userError "Iroh subdivided group")
  require "Iroh subdivided group uses actual chunk counters"
    (part.frame.fields.map List.length == [64, 64, 64, 64, 64, 64, 1024])
  require "Iroh trusted interior bytes"
    ((part.frame.body.trustedRange? 32769 ⟨1024, 1024⟩).map visible == some (zeros 1024))
  require "Iroh interior does not prove EOF" part.frame.body.final.eof.isNone
  let some edge := checkIrohRawGet? cap root edgeReq past |
    throw (IO.userError "Iroh clamped edge")
  require "Iroh clipped past-end response authenticates final chunk" edge.frame.body.final.eof.isSome
  require "Iroh wrong root" (checkIrohRawGet? cap (zeros 32) fullReq full).isNone
  require "Iroh malformed canonical request" (checkIrohRawGet? cap root (partialReq ++ [0]) subdivided).isNone
  require "Iroh wrong response schedule" (checkIrohRawGet? cap root partialReq full).isNone
  require "Iroh truncated response" (checkIrohRawGet? cap root partialReq (subdivided.take 1415)).isNone
  require "Iroh extra body" (checkIrohRawGet? cap root partialReq (subdivided ++ [0])).isNone
  require "Iroh substituted chunk" (checkIrohRawGet? cap root partialReq (subdivided.take 1415 ++ [1])).isNone
  let some falsePrefix := checkIrohRawGet? cap root partialReq (relength 32770 subdivided) |
    throw (IO.userError "Iroh false-length interior edge shape")
  require "Iroh false length stays unauthenticated" falsePrefix.frame.body.final.eof.isNone
  require "Iroh false length matching padding rejected"
    (checkIrohRawGet? cap root edgeReq (relength 32770 past ++ [0])).isNone

#eval do
  let size := 17409
  let root := unhex "50bc54238ac9271c9f3471f5206a04eb25d2e26b3214ed971cc55230b0d22864"
  let rootPair := unhex ("5384f9b342c6cb86badedcbe662b0e980476a8db17db3cc1f13b19329749ab1fc" ++
    "650236f692c3a667617ea8edb84f6e91f0b6054c26ebbf23d3b2a589b399247")
  let payload := (List.range size).map (fun index => UInt8.ofNat (index % 251))
  let right := payload.drop 16384
  let wire := Bao.putLE64 size ++ rootPair ++ right
  let request := 0 :: root ++ [2, 0, 1, 16, 1, 0]
  let some checked := checkIrohRawGet? size root request wire |
    throw (IO.userError "Iroh short multi-chunk final group")
  require "Iroh short multi-chunk group was emitted as one data field"
    (checked.frame.fields.map List.length == [64, 1025])
  require "Iroh short multi-chunk group has independently verified final byte"
    ((checked.frame.body.verifiedRange? ⟨17408, 1⟩).map verifiedVisible ==
      some (payload.drop 17408))

#eval do
  let (root, combined, _, _, _) := Iroh.Vectors.baoFixtures
  let size := 2049
  let request : Bao.RangeRequest := ⟨1023, 1026⟩
  let some state := begin? size 4096 root (Bao.fullPlan size 1) | throw (IO.userError "stream begin")
  let some mislabeled := begin? size 4096 root (.fork ⟨1, 3⟩ .skip .skip) |
    throw (IO.userError "stream mislabeled plan begin")
  require "matching raw pair is not accepted at the wrong coordinates"
    (readStep? mislabeled (combined.drop 8)).isNone
  let step := readRangeStep? (digest := root) (size := size) request
  let some rootPair := step request.start state (combined.drop 8) | throw (IO.userError "stream root pair")
  let some leftPair := step rootPair.next rootPair.raw.next rootPair.raw.rest |
    throw (IO.userError "stream left pair")
  let some first := step leftPair.next leftPair.raw.next leftPair.raw.rest | throw (IO.userError "stream first chunk")
  require "stream first emitted offset and length"
    (first.advance.released.map position == some (1023, 1))
  require "stream rejects gap" (step (first.next + 1) first.raw.next first.raw.rest).isNone
  require "stream rejects overlap" (step (first.next - 1) first.raw.next first.raw.rest).isNone
  let some middle := step first.next first.raw.next first.raw.rest | throw (IO.userError "stream middle chunk")
  require "stream middle emitted offset and length"
    (middle.advance.released.map position == some (1024, 1024))
  require "stream not complete without final chunk" (!rangeFinished request middle.next middle.raw.next [] true)
  require "stream detects truncation" (step middle.next middle.raw.next []).isNone
  require "stream detects corrupt last chunk" (step middle.next middle.raw.next [1]).isNone
  require "stream prefix evidence remains available" (middle.advance.released.isSome && middle.raw.next.eof.isNone)
  require "stream prefix trusted promotion without completion"
    ((middle.trustedSpan? size).isSome && (middle.trustedSpan? (size + 1)).isNone)
  let some last := step middle.next middle.raw.next middle.raw.rest | throw (IO.userError "stream final chunk")
  require "stream complete" (rangeFinished request last.next last.raw.next last.raw.rest true)
  require "stream framing separate from EOF"
    (last.raw.next.eof.isSome && !rangeFinished request last.next last.raw.next [] false &&
      !rangeFinished request last.next last.raw.next [0] true)
  let some eof := last.raw.next.eof | throw (IO.userError "stream opening did not prove EOF")
  require "checked EOF promotes earlier span without inspecting its suffix" (middle.verifiedSpan? eof).isSome

#print axioms canonicalSpan
#print axioms Anchor.openCell
#print axioms SpanFact.soundTrusted
#print axioms SpanFact.soundEOF
#print axioms ExactRange.soundTrusted
#print axioms ExactRange.soundEOF
#print axioms Advance.releasedPosition
#print axioms RangeStep.releasedTrusted
#print axioms RangeStep.releasedEOF
#print axioms Coverage.exactLength
#print axioms rangeFinished_spec
#print axioms checkBaoInline?
#print axioms checkBaoOutboard?
#print axioms checkIrohRawGet?
#print axioms readRangeStep?
#print axioms Prefix.wire
#print axioms Prefix.completed
#print axioms Silmaril.Containers.Cas.Store.blake3_wire_trusted
#print axioms Silmaril.Containers.Cas.Store.blake3_wire_eof
#print axioms Silmaril.Containers.Cas.Store.blake3_wire_span_trusted
#print axioms Silmaril.Containers.Cas.Store.blake3_wire_span_eof
