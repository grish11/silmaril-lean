module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Defs

/-! Independent full V1/V2 files, including an all-null binary page in
each group and two distinct failures in a later selected page. -/

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength

open Silmaril.Formats

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int32-delta-length-group/plain-int32-delta-length-v1.parquet"⟩
private def v2 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int32-delta-length-group/plain-int32-delta-length-v2.parquet"⟩
private def badTag : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int32-delta-length-group/plain-int32-delta-length-v2-bad-tag.parquet"⟩
private def badLength : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int32-delta-length-group/plain-int32-delta-length-v2-bad-length.parquet"⟩

private def expected (group : Nat) : List Int32ByteArrayGroup.Row :=
  let g := group.toUInt8
  let values : List (Option (List UInt8)) :=
    [some [], none, some [0xFF, 0, 0x80, g], some (List.replicate 48 120 ++ [g]),
      none, none, none, none, some [0, g], some [0xC3, 0xA9, g], none,
      some (List.replicate 36 121 ++ [g])]
  values.zipIdx.map fun (value, row) =>
    (some (Int32.ofNat (12 * group + row)), value.map Bytes.ofList)

private def clean (label : String) (input : Bytes) : IO Unit := do
  let .ok checked := openFile {} input "ordinal" "payload" |
    throw (IO.userError "expected two checked selections")
  unless checked.int32Binding.columnOrdinal == 0 && checked.byteArrayBinding.columnOrdinal == 1 do
    throw (IO.userError "wrong original chunk association")
  unless [0, 1, 2].mapM (readGroup checked {}) == .ok ([0, 1, 2].map expected) do
    throw (IO.userError "wrong exact row pairing")
  IO.println s!"{label}: 36 exact pairs, including three all-null binary pages"

#eval clean "V1" v1
#eval clean "V2" v2

private def damaged (label : String) (input : Bytes) (reason : FlatColumn.PageError PageError) : IO Unit := do
  let .error actual := readFileRowGroup {} input "ordinal" "payload" 1 |
    throw (IO.userError "damaged input returned a group")
  unless actual == .byteArray (.page 1 1 "payload" 2 760 reason) do
    throw (IO.userError s!"wrong indexed error: {reprStr actual}")
  let .ok checked := openFile {} input "ordinal" "payload" | throw (IO.userError "damaged metadata")
  unless checked.readInt32 {} 1 == .ok ((expected 1).map Prod.fst) &&
      [0, 2].mapM (readGroup checked {}) == .ok ([0, 2].map expected) do
    throw (IO.userError "unaffected column or group differs")
  IO.println s!"{label}: group 1 column 1 page 2 header 760, {reprStr reason}"

#eval damaged "V2 wrong tag" badTag (.encoding 3)
#eval damaged "V2 short value payload" badLength (.decode (.delta (.lengthByteArray .truncated)))

#guard v2.data[776]! == 12 && badTag.data == v2.data.set! 776 6
#guard v2.data[792]! == 4 && badLength.data == v2.data.set! 792 6

-- The PLAIN entry point retains its admission policy.
#guard Int32ByteArrayGroup.readFileRowGroup {} v2 ⟨"ordinal", .required⟩ ⟨"payload", .optional⟩ 1 =
  .error (.byteArray (.column 1 1 "payload" .encodings))

#guard readFileRowGroup {} v2 "ordinal" "payload" 3 = .error (.int32 (.groupIndex 3))
#guard readFileRowGroup {} v2 "ordinal" "decoy" 1 =
  .error (.openFailure (.bind .byteArray (.leafMismatch 2 ⟨"decoy", .byteArray, .optional⟩)))

#guard badLength.data[588]! == 0
#guard readFileRowGroup {} ⟨badLength.data.set! 588 6⟩ "ordinal" "payload" 1 =
  .error (.int32 (.page 1 0 "ordinal" 1 574 (.encoding 3)))

#guard readFileRowGroup { group := { maxValueBytes := 1 } } v2 "ordinal" "payload" 0 =
  .error (.byteArray (.page 0 1 "payload" 0 100 (.decode (.delta (.lengthByteArray .valueLimit)))))

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength
