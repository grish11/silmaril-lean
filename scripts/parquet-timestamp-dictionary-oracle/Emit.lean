module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Defs

open Silmaril Silmaril.Formats Silmaril.Numeric.Timestamp
open Silmaril.Formats.Parquet.Timestamp

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

private abbrev convert := Leaf.Dictionary.convert

private def checkLate (wire : Bytes) (pageOffset : Nat) : IO Unit := do
  let cause : Leaf.Events.Error :=
    .groupFailure 2 (.dictionaryPage 1 pageOffset (.references (.outOfBounds 3)))
  let bound ← require (Leaf.openLeafWith .allowConvertedOnly {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Dictionary.readBound {} {} bound)
  if width : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, width⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts ==
        [[some (-9223372036854775808), none, some (-1), some (-9223372036854775808),
          some 9223372036854775807, some (-1)], [some 0, some (-7), none, some 0, some 8, none]] do
      throw (IO.userError "late bad reference lost its complete prefix")
  else throw (IO.userError "missing TIMESTAMP field")
  match trace.termination with
  | .readError actual => unless actual == cause do throw (IO.userError s!"unexpected {repr actual}")
  | _ => throw (IO.userError "expected a typed late read error")
  expectError "late source error before IPC admission" (.source cause)
    (convert .allowConvertedOnly {} {} {ipc.batches := 0} wire 2)

public def main (args : List String) : IO Unit := do
  let [folder, badHeader, fallbackIndex, fallbackHeader] := args |
    throw (IO.userError "usage: Emit.lean DIRECTORY BAD_HEADER FALLBACK_INDEX FALLBACK_HEADER")
  let some badOffset := badHeader.toNat? | throw (IO.userError "invalid bad page offset")
  let some plainIndex := fallbackIndex.toNat? | throw (IO.userError "invalid PLAIN page index")
  let some plainOffset := fallbackHeader.toNat? | throw (IO.userError "invalid PLAIN page offset")
  let directory : System.FilePath := folder
  let cases : List (String × AnnotationProfile) :=
    [("v1", .modernOnly), ("v2", .modernOnly), ("legacy", .allowConvertedOnly)]
  for (name, profile) in cases do
    let wire ← input directory name
    let output ← require (convert profile {} {} {} wire 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray
  let wire ← input directory "v1"
  expectError "default PLAIN policy" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Events.ToIpc.convert {} {} wire 2)
  expectError "converted-only opt-in required" (.source (.openFailure (.annotation (.missingField 10))))
    (convert .modernOnly {} {} {} (← input directory "legacy") 2)
  expectError "wrong selected physical type" (.source (.openFailure (.annotation .notInt64Leaf)))
    (convert .modernOnly {} {} {} wire 1)
  expectError "compressed dictionary profile" (.source (.groupFailure 0 (.chunkCodec 1)))
    (convert .modernOnly {} {leaf.allowSnappy := true} {} (← input directory "snappy") 2)
  expectError "genuine writer PLAIN fallback"
    (.source (.groupFailure 0 (.dictionaryPage plainIndex plainOffset (.encoding 0))))
    (convert .modernOnly {} {} {} (← input directory "fallback") 2)
  expectError "chunk byte cap" (.source (.groupFailure 0 .dictionaryChunkLimit))
    (convert .modernOnly {maxChunkBytes := 0} {} {} wire 2)
  expectError "dictionary frame counts toward page cap" (.source (.groupFailure 0 (.framing .pageLimit)))
    (convert .modernOnly {} {leaf.framing.maxPages := 1} {} wire 2)
  let bound ← require (Leaf.openLeaf {} wire 2)
  let chunk ← require (Leaf.Dictionary.checkGroup {} {} bound 0)
  let dictOffset := chunk.dictionary.header.start
  let page :: _ := chunk.data | throw (IO.userError "missing first data page")
  expectError "dictionary entry cap" (.source (.groupFailure 0 (.dictionaryPage 0 dictOffset .entryLimit)))
    (convert .modernOnly {maxEntries := 2} {} {} wire 2)
  expectError "dictionary body cap" (.source (.groupFailure 0 (.dictionaryPage 0 dictOffset .byteLimit)))
    (convert .modernOnly {maxDictionaryBytes := 23} {} {} wire 2)
  expectError "index byte cap"
    (.source (.groupFailure 0 (.dictionaryPage 1 page.frame.header.start (.references .indexByteLimit))))
    (convert .modernOnly {indices := ⟨1024 * 1024, 0⟩} {} {} wire 2)
  checkLate (← input directory "bad") badOffset
  IO.println "Eleven typed refusals and the complete late-error event prefix passed"
