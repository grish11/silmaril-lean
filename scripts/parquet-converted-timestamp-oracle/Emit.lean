module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Numeric.Timestamp
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

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

private def observeEvents (bound : Leaf.Bound) :
    IO (List (List (Option Int)) × Arrow.Events.Termination Leaf.Events.Error) := do
  let ⟨schema, trace⟩ ← require (Leaf.Events.readBound {} bound)
  if positive : 0 < schema.width then
    let batches := batchesAt trace ⟨0, positive⟩
    return (batches.map Arrow.TimestampBatch.Writer.tickCounts, trace.termination)
  else throw (IO.userError "expected one field")

private def positive (directory : System.FilePath) (name : String) (ordinal : Nat) (unit : TickUnit)
    (zone : Option String) : IO Unit := do
  let wire ← input directory name
  let bound ← require (Leaf.openLeafWith .allowConvertedOnly {} wire ordinal)
  let binding := selectedBinding bound
  unless binding.metadata.unit == unit && binding.metadata.timezone == zone do
    throw (IO.userError s!"{name}: wrong bound descriptor")
  let groups ← require ((List.range bound.snapshot.groupCount).mapM (Leaf.readGroup {} bound))
  let (batches, terminal) ← observeEvents bound
  match terminal with
  | .eos =>
    unless batches == groups.map (List.map (Option.map Ticks.ticks)) do
      throw (IO.userError s!"{name}: events differ from checked groups")
  | _ => throw (IO.userError s!"{name}: expected EOS")
  let output ← require (convertWith .allowConvertedOnly {} {} wire ordinal)
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "usage: Emit.lean DIRECTORY")
  let directory : System.FilePath := folder
  positive directory "millis_v1" 3 .millisecond (some "UTC")
  positive directory "micros_v2" 1 .microsecond (some "UTC")
  positive directory "modern_local" 2 .millisecond none
  let millis ← input directory "millis_v1"
  let micros ← input directory "micros_v2"
  expectError "modern default" (.source (.openFailure (.annotation (.missingField 10))))
    (convert {} {} millis 3)
  expectError "wrong physical leaf" (.source (.openFailure (.annotation .notInt64Leaf)))
    (convertWith .allowConvertedOnly {} {} millis 1)
  expectError "group budget counts the empty group" (.groupLimit 2 3)
    (convertWith .allowConvertedOnly {maxGroups := 2} {} micros 1)
  expectError "conflicting units" (.source (.openFailure (.annotation (.convertedType 10))))
    (convertWith .allowConvertedOnly {} {} (← input directory "conflicting_dual") 2)
  expectError "present wrong modern union" (.source (.openFailure (.annotation .logicalUnion)))
    (convertWith .allowConvertedOnly {} {} (← input directory "bad_modern") 1)
  expectError "unrelated converted type" (.source (.openFailure (.annotation (.convertedType 11))))
    (convertWith .allowConvertedOnly {} {} (← input directory "unrelated_code") 1)
  expectError "absent annotations" (.source (.openFailure (.annotation (.missingField 6))))
    (convertWith .allowConvertedOnly {} {} (← input directory "unannotated_int64") 1)
  let late ← input directory "late_page"
  let cause : Leaf.Events.Error := .groupFailure 2 (.page 0 (.scalar (.unsupportedEncoding 8)))
  expectError "source error before output buffer cap" (.source cause)
    (convertWith .allowConvertedOnly {} {ipc.bodyBytes := 0} late 1)
  let bound ← require (Leaf.openLeafWith .allowConvertedOnly {} late 1)
  let (batches, terminal) ← observeEvents bound
  match terminal with
  | .readError actual =>
    unless actual == cause && batches == [[some (-9223372036854775808), some (-1001)], []] do
      throw (IO.userError "late failure lost its complete event prefix")
  | _ => throw (IO.userError "expected a typed late read error")
  IO.println "Eight typed refusals and the complete late-error event prefix passed"
