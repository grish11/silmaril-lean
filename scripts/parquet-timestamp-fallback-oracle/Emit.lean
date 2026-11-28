module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs

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

private def convert (wire : Bytes) : Except Leaf.Events.ToIpc.Error KBytes :=
  Leaf.Fallback.convert .modernOnly {} {} {} wire 2

private def expectedFirst : List (Option Int) :=
  [some (-9223372036854775808), none, some (-11), some 9223372036854775807] ++
    (List.range 20).map fun index => if index % 5 = 2 then none else some (Int.ofNat index - 100)

private def checkLate (wire : Bytes) (offset : Nat) : IO Unit := do
  let cause : Leaf.Events.Error := .groupFailure 1 (.dictionaryPage 6 offset (.plain (.plain .truncated)))
  let bound ← require (Leaf.openLeaf {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Fallback.readBound {} {} bound)
  if column : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, column⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts == [expectedFirst] do
      throw (IO.userError "late PLAIN failure lost its complete group prefix")
  else throw (IO.userError "missing TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == cause do throw (IO.userError s!"unexpected late failure {repr actual}")
  | _ => throw (IO.userError "expected terminal PLAIN decoder error")
  expectError "late source error precedes IPC admission" (.source cause)
    (Leaf.Fallback.convert .modernOnly {} {} {ipc.batches := 0} wire 2)

public def main (args : List String) : IO Unit := do
  let [folder, firstOrd, firstPlain, firstData, reentry, late] := args |
    throw (IO.userError "usage: Emit.lean DIRECTORY FIRST_ORD FIRST_PLAIN FIRST_DATA REENTRY LATE")
  let some firstOrdinal := firstOrd.toNat? | throw (IO.userError "invalid first PLAIN ordinal")
  let some firstPlainOffset := firstPlain.toNat? | throw (IO.userError "invalid first PLAIN offset")
  let some firstDataOffset := firstData.toNat? | throw (IO.userError "invalid first data offset")
  let some reentryOffset := reentry.toNat? | throw (IO.userError "invalid reentry offset")
  let some lateOffset := late.toNat? | throw (IO.userError "invalid late PLAIN offset")
  let directory : System.FilePath := folder
  for name in ["existing", "v1", "v2"] do
    let output ← require (convert (← input directory name))
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray
  let existing ← input directory "existing"
  expectError "PLAIN default" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Events.ToIpc.convert {} {} existing 2)
  expectError "dictionary-only default"
    (.source (.groupFailure 0 (.dictionaryPage firstOrdinal firstPlainOffset (.encoding 0))))
    (Leaf.Dictionary.convert .modernOnly {} {} {} existing 2)
  expectError "fallback is required" (.source (.groupFailure 0 .dictionaryMissingFallback))
    (convert (← input directory "dictionary_only"))
  expectError "PLAIN first" (.source (.groupFailure 0 (.dictionaryPage 1 firstDataOffset (.encoding 0))))
    (convert (← input directory "plain_first"))
  expectError "dictionary after PLAIN"
    (.source (.groupFailure 0 (.dictionaryPage 3 reentryOffset .dictionaryAfterFallback)))
    (convert (← input directory "reentry"))
  expectError "compressed dictionary" (.source (.groupFailure 0 (.chunkCodec 1)))
    (Leaf.Fallback.convert .modernOnly {} {leaf.allowSnappy := true} {} (← input directory "compressed") 2)
  checkLate (← input directory "bad") lateOffset
  IO.println "Seven typed refusals and the complete earlier group passed"
