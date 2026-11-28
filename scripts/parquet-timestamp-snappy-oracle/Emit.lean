module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Numeric.Timestamp
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private def limits : Leaf.Events.ToIpc.Limits := { leaf.allowSnappy := true }

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expectError (label : String) (expected : Leaf.Events.ToIpc.Error)
    (result : Except Leaf.Events.ToIpc.Error KBytes) : IO Unit := do
  match result with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected output")

private def checkPageCaps (profile : AnnotationProfile) (wire : Bytes) : IO Unit := do
  let bound ← require (openBoundWith profile limits wire 1)
  let chunk ← require (Leaf.selectChunk limits.leaf bound 0)
  let frames ← require (Parquet.Page.readChunk limits.leaf.framing bound.snapshot.bytes chunk.span)
  let first :: _ := frames | throw (IO.userError "expected first data page")
  unless first.value.compressedSize > 0 && first.value.uncompressedSize > 0 do
    throw (IO.userError "expected nonempty first data page")
  expectError "compressed cap" (.source (.groupFailure 0 (.page 0 (.scalar (.payload .compressedLimit)))))
    (convertWith profile { limits with leaf.page.compressedBytes := first.value.compressedSize - 1 } {}
      wire 1)
  expectError "expanded cap" (.source (.groupFailure 0 (.page 0 (.scalar (.payload .outputLimit)))))
    (convertWith profile { limits with leaf.page.uncompressedBytes := first.value.uncompressedSize - 1 } {}
      wire 1)

private def checkLate (profile : AnnotationProfile) (wire : Bytes) : IO Unit := do
  let cause : Leaf.Events.Error := .groupFailure 2 (.page 1 (.scalar (.payload .outputSizeMismatch)))
  let bound ← require (openBoundWith profile limits wire 1)
  let prior ← require ([0, 1].mapM (Leaf.readGroup limits.leaf bound))
  let ⟨schema, trace⟩ ← require (Leaf.Events.readBound limits.leaf bound)
  if positive : 0 < schema.width then
    let observed := (batchesAt trace ⟨0, positive⟩).map Arrow.TimestampBatch.Writer.tickCounts
    let expected := prior.map (List.map (Option.map Ticks.ticks))
    unless observed == expected && observed.length == 2 &&
        observed[0]?.map (·.take 2) == some [some (-9223372036854775808), some 9223372036854775807] &&
        observed[1]? == some (List.replicate 32 none) do
      throw (IO.userError "late Snappy failure lost the exact event prefix")
  else throw (IO.userError "expected timestamp field")
  match trace.termination with
  | .readError actual => unless actual == cause do throw (IO.userError s!"unexpected {repr actual}")
  | _ => throw (IO.userError "expected original indexed Snappy size error")
  expectError "late source error precedes output admission" (.source cause)
    (convertWith profile limits { ipc.batches := 0 } wire 1)

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "usage: Emit.lean DIRECTORY")
  let directory : System.FilePath := folder
  let admitted : List (String × AnnotationProfile) :=
    [("modern_v1", .modernOnly), ("modern_v2", .modernOnly), ("legacy_v2", .allowConvertedOnly)]
  for (name, profile) in admitted do
    let wire ← input directory name
    let output ← require (convertWith profile limits {} wire 1)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray
  let v1 ← input directory "modern_v1"
  let v2 ← input directory "legacy_v2"
  expectError "default codec refusal" (.source (.groupFailure 0 (.chunkCodec 1)))
    (convert {} {} v1 1)
  expectError "codec opt-in retains default annotation refusal"
    (.source (.openFailure (.annotation (.missingField 10)))) (convert limits {} v2 1)
  expectError "annotation opt-in retains default codec refusal" (.source (.groupFailure 0 (.chunkCodec 1)))
    (convertWith .allowConvertedOnly {} {} v2 1)
  expectError "group budget" (.groupLimit 2 3) (convert { limits with maxGroups := 2 } {} v1 1)
  checkPageCaps .modernOnly v1
  checkPageCaps .allowConvertedOnly v2
  checkLate .modernOnly (← input directory "bad_v1")
  checkLate .allowConvertedOnly (← input directory "bad_v2")
  IO.println "Ten typed refusals and both complete two-group prefixes passed"
