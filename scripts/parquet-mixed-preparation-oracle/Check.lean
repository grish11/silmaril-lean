module

import Lean.Data.Json
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare.Defs
meta import Lean.Data.Json
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare.Defs

open Lean (Json toJson)
open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare

private def ordinal : Field := ⟨"ordinal", .required⟩
private def nullableOrdinal : Field := ⟨"ordinal", .optional⟩
private def payload : Field := ⟨"payload", .optional⟩
private def key : Field := ⟨"key", .required⟩

private def load (directory : System.FilePath) (file : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / file)⟩

private def observation (input : Bytes) (int32 binary : Field) : IO Json := do
  let .ok value := prepare {} input int32 binary | throw (IO.userError "source preparation failed")
  unless value.schema.fields == [⟨int32.name, int32.layout == .optional, .primitive .int32⟩,
      ⟨binary.name, binary.layout == .optional, .view .binary⟩] do
    throw (IO.userError "wrong INT32-first descriptor")
  let groups := value.batches.map fun batch => Json.mkObj [
    ("rows", toJson batch.rowCount),
    ("ints", toJson (batch.intValues.map (Option.map Int32.toInt))),
    ("bytes", toJson (batch.viewValues.map (Option.map (List.map UInt8.toNat ∘ KBytes.toList))))]
  return Json.mkObj [
    ("intName", toJson value.schema.intName), ("intNullable", toJson value.schema.intNullable),
    ("viewName", toJson value.schema.viewName), ("viewNullable", toJson value.schema.viewNullable),
    ("groups", toJson groups)]

private def checkLate (limits : File.Limits) (input : Bytes) (cause : File.Error)
    (counts : List Nat) : IO Unit := do
  let .error error := prepare limits input ordinal payload
    | throw (IO.userError "failed source unexpectedly returned prepared batches")
  unless error == cause do throw (IO.userError "preparation changed the original indexed error")
  let .ok ⟨_, trace⟩ := Reader.readAll (File.openSource limits input ordinal payload)
    | throw (IO.userError "index error lost the opened source")
  unless trace.batches.map (·.rowCount) == counts && trace.termination == .readError cause do
    throw (IO.userError "the separate trace lost its complete prefix or terminal cause")

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let directory := System.FilePath.mk path
  let v1 ← load directory "plain-byte-array-v1.parquet"
  let v2 ← load directory "plain-byte-array-v2.parquet"
  let badV1 ← load directory "plain-byte-array-v1-bad-length.parquet"
  let badV2 ← load directory "plain-byte-array-v2-bad-length.parquet"
  let emptyMiddle ← load directory "empty-middle-v2.parquet"
  let optional ← load directory "nullable-int32-v2.parquet"
  let schemaOnly ← load directory "mixed-schema-only.parquet"

  let .error (.fileRowLimit 35 36) := prepare { maxFileRows := 35 } badV2 ordinal payload
    | throw (IO.userError "the file row cap did not precede corrupted page decoding")
  let .error (.openFailure (.bind .byteArray (.unknownLeaf "missing"))) :=
    prepare { maxFileRows := 0 } badV2 ordinal ⟨"missing", .optional⟩
    | throw (IO.userError "checked selection did not precede the file row cap")
  let .error (.openFailure (.fileByteLimit 4 actual)) :=
    prepare { group := { maxFileBytes := 4 }, maxFileRows := 0 } badV2 ordinal ordinal
    | throw (IO.userError "the byte cap did not precede duplicate selection and row caps")
  unless actual == badV2.length do throw (IO.userError "wrong byte count in the cap failure")

  let savedV1 := File.Error.groupFailure 1
    (.byteArray (.page 1 1 "payload" 1 608 (.decode (.scalar (.plain .truncated)))))
  let savedV2 := File.Error.groupFailure 1
    (.byteArray (.page 1 1 "payload" 1 646 (.decode (.scalar (.plain .truncated)))))
  checkLate { maxFileRows := 36 } badV1 savedV1 [12]
  checkLate { maxFileRows := 36 } badV2 savedV2 [12]
  unless badV2.data[527]! == 0 && emptyMiddle.data[122]! == 0 do
    throw (IO.userError "wrong original page tags in corruption controls")
  checkLate {} ⟨badV2.data.set! 527 6⟩
    (.groupFailure 1 (.int32 (.page 1 0 "ordinal" 1 513 (.encoding 3)))) [12]
  let lateEmpty : Bytes := ⟨emptyMiddle.data.set! 122 6⟩
  let .error (.fileRowLimit 4 5) := prepare { maxFileRows := 4 } lateEmpty ordinal payload
    | throw (IO.userError "wrong cap for the file with an empty middle group")
  checkLate { maxFileRows := 5 } lateEmpty
    (.groupFailure 2 (.byteArray (.page 2 1 "payload" 0 108 (.encoding 3)))) [3, 0]

  let observed ← [
    (v1, ordinal, payload), (v2, ordinal, payload), (badV2, ordinal, key),
    (emptyMiddle, ordinal, payload), (optional, nullableOrdinal, key),
    (schemaOnly, nullableOrdinal, key)].mapM fun (input, int32, binary) => observation input int32 binary
  IO.println (toJson observed).compress
