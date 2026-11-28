module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Defs

/-! Exact source batches across paired footer groups, including an empty group
between nonempty ones and selected failures after a complete earlier group. -/

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.File

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v1.parquet"⟩
private def v2 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2.parquet"⟩
private def badV1 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v1-bad-length.parquet"⟩
private def badV2 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2-bad-length.parquet"⟩
private def emptyMiddle : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def key : Field := ⟨"key", .required⟩

private def expected (group : Nat) (binary : Field) : List Int32ByteArrayGroup.Row :=
  let g := group.toUInt8
  let raw : List (Option (List UInt8)) :=
    if binary.layout = .optional then
      [some [], none, some [0xFF, 0, 0x80, g], some (List.replicate 48 120 ++ [g]),
        none, none, none, none, some [0, g], some [0xC3, 0xA9, g], none,
        some (List.replicate 36 121 ++ [g])]
    else
      (List.range 12).map fun row => some (if row = 0 then []
        else (List.replicate (1 + row % 5) [0x80 + g, row.toUInt8]).flatten)
  raw.zipIdx.map fun (value, row) =>
    (some (Int32.ofNat (12 * group + row)), value.map Bytes.ofList)

private def observeRow {selected : Scan.Schema String Kind} (row : Scan.Row selected Value) :
    List (Sum (Option Int32) (Option Bytes)) :=
  List.ofFn fun i =>
    match kind : (selected.kind i).2 with
    | .int32 _ => .inl (cast (congrArg (fun k => Option (Value k)) kind) (row i))
    | .byteArray _ => .inr (cast (congrArg (fun k => Option (Value k)) kind) (row i))

private def verify (limits : Limits) (input : Bytes) (binary : Field)
    (groups : List (List Int32ByteArrayGroup.Row)) (outcome : Events.Termination Error) : IO Unit := do
  let .ok ⟨selected, trace⟩ := Reader.readAll (openSource limits input ordinal binary) |
    throw (IO.userError "source failed to open")
  unless List.ofFn selected.kind == [(ordinal.name, .int32 .required), (binary.name, .byteArray binary.layout)] do
    throw (IO.userError "wrong source schema")
  let observed := trace.batches.map fun batch => batch.toRows.map observeRow
  let reference := groups.map fun group => group.map fun pair => [Sum.inl pair.1, Sum.inr pair.2]
  unless observed == reference && trace.batches.map (·.rowCount) == groups.map List.length do
    throw (IO.userError "wrong pairs or footer batch boundaries")
  unless trace.termination == outcome do throw (IO.userError "wrong first error or EOS")

private def check (label : String) (source damaged : Bytes) (header : Nat) : IO Unit := do
  verify { maxFileRows := 36 } source payload ([0, 1, 2].map fun group => expected group payload) .eos
  let failure := Error.groupFailure 1
    (.byteArray (.page 1 1 "payload" 1 header (.decode (.scalar (.plain .truncated)))))
  verify { maxFileRows := 36 } damaged payload [expected 0 payload] (.readError failure)
  verify {} damaged key ([0, 1, 2].map fun group => expected group key) .eos
  let .error (.fileRowLimit 35 36) :=
    Reader.readAll (openSource { maxFileRows := 35 } damaged ordinal payload) |
    throw (IO.userError "row cap did not precede selected page corruption")
  IO.println s!"{label}: [12, 12, 12] exact pairs, selected error after 12 rows, unselected and cap controls passed"

#eval check "V1" v1 badV1 608
#eval check "V2" v2 badV2 646

#guard badV2.data[527]! == 0
#eval verify {} ⟨badV2.data.set! 527 6⟩ payload [expected 0 payload]
  (.readError (.groupFailure 1 (.int32 (.page 1 0 "ordinal" 1 513 (.encoding 3)))))

#eval do
  let groups : List (List Int32ByteArrayGroup.Row) :=
    [[(some (-2147483648), none), (some 0, some .empty), (some 17, some (Bytes.ofList [0xFF, 0]))],
      [], [(some 2147483647, some (Bytes.ofList [0x80])), (some (-1), some (Bytes.ofList [120, 121]))]]
  verify { maxFileRows := 5 } emptyMiddle payload groups .eos
  unless emptyMiddle.data[122]! == 0 do throw (IO.userError "wrong last-group encoding byte")
  verify { maxFileRows := 5 } ⟨emptyMiddle.data.set! 122 6⟩ payload (groups.take 2)
    (.readError (.groupFailure 2 (.byteArray (.page 2 1 "payload" 0 108 (.encoding 3)))))
  IO.println "V2 empty-group control: exact [3, 0, 2] at EOS and [3, 0] before the last-group failure"

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.File
