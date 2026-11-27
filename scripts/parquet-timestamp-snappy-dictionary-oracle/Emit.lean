module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs

open Silmaril Silmaril.Formats
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

private abbrev convert := Leaf.Dictionary.Snappy.convert

private def expectedFirst : List (Option Int) :=
  (List.replicate 30 [some (-9223372036854775808), none, some (-1), some (-9223372036854775808),
    some 9223372036854775807, some (-1)]).flatten

private def checkLate (profile : AnnotationProfile) (wire : Bytes) (error : Leaf.Error) : IO Unit := do
  let cause : Leaf.Events.Error := .groupFailure 2 error
  let bound ← require (Leaf.openLeafWith profile {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Dictionary.Snappy.readBound {} {} bound)
  if column : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, column⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts ==
        [expectedFirst, [some 0, some (-7), none, some 0, some 8, none]] do
      throw (IO.userError "late Snappy failure lost its complete progress")
  else throw (IO.userError "missing TIMESTAMP field")
  match trace.termination with
  | .readError actual => unless actual == cause do throw (IO.userError s!"unexpected {repr actual}")
  | _ => throw (IO.userError "expected original indexed Snappy error")
  expectError "source error precedes IPC admission" (.source cause)
    (convert profile {} {} {ipc.batches := 0} wire 2)

private def checkCaps (wire : Bytes) : IO Unit := do
  let bound ← require (Leaf.openLeaf {} wire 2)
  let first ← require (Leaf.Dictionary.Snappy.checkGroup {} {} bound 0)
  let page :: _ := first.data | throw (IO.userError "expected first dictionary data page")
  let settings : Leaf.Events.ToIpc.Limits := {}
  let stored := first.dictionary.value.compressedSize
  let expanded := first.dictionary.value.uncompressedSize
  let dict := Leaf.Error.dictionaryPage 0 first.dictionary.header.start
  let data := Leaf.Error.dictionaryPage 1 page.frame.header.start
  expectError "dictionary expanded limit" (.source (.groupFailure 0 (dict (.payload .outputLimit))))
    (convert .modernOnly {maxDictionaryBytes := 1} {} {} wire 2)
  expectError "dictionary stored limit" (.source (.groupFailure 0 (dict (.checksumFailure .byteLimit))))
    (convert .modernOnly {} {settings with leaf.page.compressedBytes := 0} {} wire 2)
  expectError "dictionary entry limit" (.source (.groupFailure 0 (dict .entryLimit)))
    (convert .modernOnly {maxEntries := 2} {} {} wire 2)
  expectError "data expanded limit" (.source (.groupFailure 0 (data (.references (.page (.payload .outputLimit))))))
    (convert .modernOnly {} {settings with leaf.page.uncompressedBytes := expanded} {} wire 2)
  expectError "data stored limit" (.source (.groupFailure 0 (data (.checksumFailure .byteLimit))))
    (convert .modernOnly {} {settings with leaf.page.compressedBytes := stored} {} wire 2)

public def main (args : List String) : IO Unit := do
  let folder :: rest := args | throw (IO.userError "expected directory and indexed error evidence")
  let some [dictOffset, dictCRC, dictActual, levelOffset, levelCRC, levelActual, suffixOffset,
    plainOrdinal, plainOffset] := rest.mapM String.toNat? | throw (IO.userError "invalid error evidence")
  let directory : System.FilePath := folder
  let cases : List (String × AnnotationProfile) :=
    [("v1", .modernOnly), ("v2", .modernOnly), ("legacy", .allowConvertedOnly)]
  for (name, profile) in cases do
    let output ← require (convert profile {} {} {} (← input directory name) 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

  let wire ← input directory "v1"
  expectError "uncompressed dictionary default" (.source (.groupFailure 0 (.chunkCodec 1)))
    (Leaf.Dictionary.convert .modernOnly {} {leaf.allowSnappy := true} {} wire 2)
  expectError "uncompressed fallback default" (.source (.groupFailure 0 (.chunkCodec 1)))
    (Leaf.Fallback.convert .modernOnly {} {leaf.allowSnappy := true} {} wire 2)
  expectError "PLAIN Snappy default" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Events.ToIpc.convert {leaf.allowSnappy := true} {} wire 2)
  expectError "Snappy dictionary requires codec 1" (.source (.groupFailure 0 (.chunkCodec 0)))
    (convert .modernOnly {} {} {} (← input directory "uncompressed") 2)
  expectError "Snappy dictionary refuses PLAIN fallback"
    (.source (.groupFailure 0 (.dictionaryPage plainOrdinal plainOffset (.encoding 0))))
    (convert .modernOnly {} {} {} (← input directory "fallback") 2)
  checkCaps wire
  checkLate .modernOnly (← input directory "bad_dictionary")
    (.dictionaryPage 0 dictOffset (.checksumFailure (.mismatch (UInt32.ofNat dictCRC) (UInt32.ofNat dictActual))))
  checkLate .modernOnly (← input directory "bad_levels")
    (.dictionaryPage 1 levelOffset (.checksumFailure (.mismatch (UInt32.ofNat levelCRC) (UInt32.ofNat levelActual))))
  checkLate .allowConvertedOnly (← input directory "bad_suffix")
    (.dictionaryPage 1 suffixOffset (.references (.page (.payload .outputSizeMismatch))))
  IO.println "Thirteen typed refusals and three exact late-error prefixes passed"
