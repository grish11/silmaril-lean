module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs

/-! PyArrow V1 and V2 files with two BYTE_ARRAY columns and a leading INT32
sibling. The damaged files overdeclare one length on a later group's second page. -/

namespace Silmaril.Formats.Parquet.Plain.ByteArray.File

open Silmaril.Formats Silmaril.Formats.Arrow

private def v1 : Bytes := ⟨include_bytes "../../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2.parquet"⟩
private def badV1 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v1-bad-length.parquet"⟩
private def badV2 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2-bad-length.parquet"⟩

private def optionalSlots (group : Nat) : List (Option Bytes) :=
  let g := group.toUInt8
  ([some [], none, some [0xFF, 0, 0x80, g], some (List.replicate 48 120 ++ [g]),
    none, none, none, none, some [0, g], some [0xC3, 0xA9, g], none,
    some (List.replicate 36 121 ++ [g])] : List (Option (List UInt8))).map (Option.map Bytes.ofList)

private def requiredSlots (group : Nat) : List (Option Bytes) :=
  (List.range 12).map fun row =>
    some (Bytes.ofList (if row = 0 then []
      else (List.replicate (1 + row % 5) [0x80 + group.toUInt8, row.toUInt8]).flatten))

private def verify (source : Bytes) (name : String) (layout : FlatColumn.Layout)
    (expected : List (List (Option Bytes))) (outcome : Events.Termination Error) : IO Unit := do
  let .ok ⟨selected, trace⟩ := readAll {} source name layout |
    throw (IO.userError "file rejected at open")
  unless List.ofFn selected.kind == [(name, layout)] do throw (IO.userError "wrong selected schema")
  let observed := trace.batches.map fun batch =>
    batch.toRows.map fun value => List.ofFn fun index => value index
  unless observed == expected.map (List.map (fun value => [value])) do
    throw (IO.userError "wrong raw bytes, nullability, row order, or group boundary")
  unless trace.termination == outcome do throw (IO.userError "wrong terminal outcome")

private def clean (label : String) (source : Bytes) : IO Unit := do
  verify source "payload" .optional ([0, 1, 2].map optionalSlots) .eos
  verify source "key" .required ([0, 1, 2].map requiredSlots) .eos
  IO.println s!"{label}: 36 opaque slots per selected leaf, groups [12, 12, 12], EOS"

private def damaged (label : String) (source : Bytes) (header : Nat) : IO Unit := do
  let reason := FlatColumn.Error.page 1 1 "payload" 1 header (.decode (.scalar (.plain .truncated)))
  verify source "payload" .optional [optionalSlots 0] (.readError (.column reason))
  verify source "key" .required ([0, 1, 2].map requiredSlots) .eos
  let .ok file := openFile {} source "payload" .optional | throw (IO.userError "cannot reopen damaged file")
  unless file.readGroup {} 1 == .error reason && file.readGroup {} 2 == .ok (optionalSlots 2) do
    throw (IO.userError "indexed error or later group differs")
  IO.println s!"{label}: 12-row prefix, truncated at group 1 column 1 page 1 header {header}"

#eval clean "V1" v1
#eval clean "V2" v2
#eval damaged "damaged V1" badV1 608
#eval damaged "damaged V2" badV2 646

#guard v1.data[633]! == 2 && badV1.data == (v1.data.set! 633 255).set! 634 255
#guard v2.data[672]! == 2 && badV2.data == (v2.data.set! 672 255).set! 673 255

-- The column still advertises PLAIN and RLE. Change the selected data
-- page's value encoding from PLAIN to RLE without changing its extent.
#guard v2.data[660]! == 0
#guard match openFile {} ⟨v2.data.set! 660 6⟩ "payload" .optional with
  | .ok file => file.readGroup {} 1 = .error (.page 1 1 "payload" 1 646 (.encoding 3))
  | .error _ => False

#guard match openFile {} v2 "payload" .optional, openFile {} v2 "key" .required with
  | .ok payload, .ok key => payload.binding.columnOrdinal == 1 && payload.binding.leafOrdinal == 2 &&
      key.binding.columnOrdinal == 2 && key.binding.leafOrdinal == 3
  | _, _ => false

#guard match openFile {} v2 "payload" .required with
  | .error (.schema (.leafMismatch 1 _)) => true
  | _ => false

#guard match openFile {} v2 "ordinal" .required with
  | .error (.schema (.leafMismatch 0 _)) => true
  | _ => false

#guard match openFile {} v2 "missing" .optional with
  | .error (.schema (.unknownLeaf "missing")) => true
  | _ => false

#guard match readAll { maxFileBytes := 4 } v1 "payload" .optional with
  | .error (.fileByteLimit 4 2210) => true
  | _ => false

#guard match readAll { maxFileRows := 35 } v2 "payload" .optional with
  | .error (.fileRowLimit 35 36) => true
  | _ => false

#guard match openFile {} v2 "payload" .optional with
  | .ok file => file.readGroup { maxValueBytes := 1 } 0 =
      .error (.page 0 1 "payload" 0 100 (.decode (.scalar (.plain .valueByteLimit)))) ∧
      file.readGroup {} 3 = .error (.groupIndex 3)
  | .error _ => False

end Silmaril.Formats.Parquet.Plain.ByteArray.File
