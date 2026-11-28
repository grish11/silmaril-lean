module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.Defs

/-! Exact batches and terminal errors from the bounded fixed-tag-6 source. -/

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int32-delta-length-group/plain-int32-delta-length-v1.parquet"⟩
private def v2 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int32-delta-length-group/plain-int32-delta-length-v2.parquet"⟩
private def badTag : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int32-delta-length-group/plain-int32-delta-length-v2-bad-tag.parquet"⟩
private def badLength : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int32-delta-length-group/plain-int32-delta-length-v2-bad-length.parquet"⟩

private def expected (group : Nat) : List Int32ByteArrayGroup.Row :=
  let g := group.toUInt8
  let values : List (Option (List UInt8)) :=
    [some [], none, some [0xFF, 0, 0x80, g], some (List.replicate 48 120 ++ [g]),
      none, none, none, none, some [0, g], some [0xC3, 0xA9, g], none,
      some (List.replicate 36 121 ++ [g])]
  values.zipIdx.map fun (value, row) =>
    (some (Int32.ofNat (12 * group + row)), value.map Bytes.ofList)

private def emptyMiddle : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int32-delta-length-file/delta-length-empty-middle-v2.parquet"⟩

private def observeRow {selected : Scan.Schema String Kind} (row : Scan.Row selected Value) :
    List (Sum (Option Int32) (Option Bytes)) :=
  List.ofFn fun i =>
    match kind : (selected.kind i).2 with
    | .int32 _ => .inl (cast (congrArg (fun k => Option (Value k)) kind) (row i))
    | .byteArray _ => .inr (cast (congrArg (fun k => Option (Value k)) kind) (row i))

private def verify (limits : Limits) (input : Bytes)
    (groups : List (List Int32ByteArrayGroup.Row)) (outcome : Events.Termination Error) : IO Unit := do
  let .ok ⟨selected, trace⟩ := Reader.readAll (openSource limits input "ordinal" "payload") |
    throw (IO.userError "source failed to open")
  unless List.ofFn selected.kind == [("ordinal", .int32 .required), ("payload", .byteArray .optional)] do
    throw (IO.userError "wrong source schema")
  let observed := trace.batches.map fun batch => batch.toRows.map observeRow
  let reference := groups.map fun group => group.map fun pair => [Sum.inl pair.1, Sum.inr pair.2]
  unless observed == reference && trace.batches.map (·.rowCount) == groups.map List.length do
    throw (IO.userError "wrong pairs or footer batch boundaries")
  unless trace.termination == outcome do throw (IO.userError "wrong first error or EOS")

#eval do
  let groups := [0, 1, 2].map expected
  verify { maxFileRows := 36 } v1 groups .eos
  verify { maxFileRows := 36 } v2 groups .eos
  IO.println "V1/V2 source: exact [12, 12, 12] with null and opaque binary slots"

private def damaged (input : Bytes) (reason : FlatColumn.PageError DeltaLength.PageError) : IO Unit := do
  verify { maxFileRows := 36 } input [expected 0]
    (.readError (.groupFailure 1 (.byteArray (.page 1 1 "payload" 2 760 reason))))
  let .error (.openFailure (.fileRowLimit 35 36)) :=
    Reader.readAll (openSource { maxFileRows := 35 } input "ordinal" "payload") |
    throw (IO.userError "row cap did not precede selected page corruption")

#eval do
  damaged badTag (.encoding 3)
  damaged badLength (.decode (.delta (.lengthByteArray .truncated)))
  IO.println "V2 controls: cap 35 rejects at open, cap 36 yields [12] before the original group 1 error"

#eval do
  let groups : List (List Int32ByteArrayGroup.Row) :=
    [[(some 10, some .empty), (some (-1), none)], [], [(some 20, some (Bytes.ofList [0xFF, 0]))]]
  verify { maxFileRows := 3 } emptyMiddle groups .eos
  unless emptyMiddle.data[109]! == 12 do throw (IO.userError "wrong last-group encoding byte")
  verify { maxFileRows := 3 } ⟨emptyMiddle.data.set! 109 6⟩ (groups.take 2)
    (.readError (.groupFailure 2 (.byteArray (.page 2 1 "payload" 0 95 (.encoding 3)))))
  IO.println "V2 empty-group control: exact [2, 0, 1] at EOS and [2, 0] before the last-group failure"

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File
