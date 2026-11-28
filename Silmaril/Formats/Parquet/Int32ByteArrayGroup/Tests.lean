module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Defs

/-! Project the existing PyArrow fixtures across unequal page boundaries.
The same damaged leaf is tested as both selected and unselected. -/

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup

open Silmaril.Formats

private def v1 : Bytes := ⟨include_bytes "../../../../data/parquet-plain-byte-array-file/plain-byte-array-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2.parquet"⟩
private def badV1 : Bytes :=
  ⟨include_bytes "../../../../data/parquet-plain-byte-array-file/plain-byte-array-v1-bad-length.parquet"⟩
private def badV2 : Bytes :=
  ⟨include_bytes "../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2-bad-length.parquet"⟩

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def key : Field := ⟨"key", .required⟩

private def optionalSlots (group : Nat) : List (Option (List UInt8)) :=
  let g := group.toUInt8
  [some [], none, some [0xFF, 0, 0x80, g], some (List.replicate 48 120 ++ [g]),
    none, none, none, none, some [0, g], some [0xC3, 0xA9, g], none,
    some (List.replicate 36 121 ++ [g])]

private def requiredSlots (group : Nat) : List (Option (List UInt8)) :=
  (List.range 12).map fun row =>
    some (if row = 0 then []
      else (List.replicate (1 + row % 5) [0x80 + group.toUInt8, row.toUInt8]).flatten)

private def expected (group : Nat) (slots : List (Option (List UInt8))) : List Row :=
  slots.zipIdx.map fun (value, row) =>
    (some (Int32.ofNat (12 * group + row)), value.map Bytes.ofList)

private def check (version : String) (source damaged : Bytes) (header : Nat) : IO Unit := do
  let result := readFileRowGroup {} source ordinal payload 1
  unless result == .ok (expected 1 (optionalSlots 1)) do
    throw (IO.userError "wrong pairs across page boundaries")
  let selected := readFileRowGroup {} damaged ordinal payload 1
  unless selected == .error (.byteArray (.page 1 1 "payload" 1 header (.decode (.scalar (.plain .truncated))))) do
    throw (IO.userError "wrong selected-column failure")
  let unselected := readFileRowGroup {} damaged ordinal key 1
  unless unselected == .ok (expected 1 (requiredSlots 1)) do
    throw (IO.userError "unselected damaged leaf affected the pairs")
  IO.println s!"{version}: 12 ordered pairs, selected failure at group 1 column 1 page 1 header {header}, unselected control passed"

#eval check "V1" v1 badV1 608
#eval check "V2" v2 badV2 646

-- The INT32 tag is changed on page 1 while the optional BYTE_ARRAY length
-- is already damaged. Both errors keep their physical coordinates.
#guard v2.data[527]! == 0 && badV2.data[527]! == 0
#guard match openFile {} ⟨badV2.data.set! 527 6⟩ ordinal payload with
  | .ok checked =>
    checked.readInt32 {} 1 = .error (.page 1 0 "ordinal" 1 513 (.encoding 3)) ∧
    checked.readByteArray {} 1 = .error (.page 1 1 "payload" 1 646 (.decode (.scalar (.plain .truncated)))) ∧
    checked.readGroup {} 1 = .error (.int32 (.page 1 0 "ordinal" 1 513 (.encoding 3)))
  | .error _ => False

#guard readFileRowGroup {} v2 ordinal payload 3 = .error (.int32 (.groupIndex 3))
#guard readFileRowGroup {} v2 ordinal ordinal 1 = .error (.duplicateName "ordinal")
#guard readFileRowGroup {} v2 key payload 1 = .error (.bind .int32 (.leafMismatch 2 ⟨"key", .int32, .required⟩))
#guard readFileRowGroup {} v2 ordinal ⟨"payload", .required⟩ 1 =
  .error (.bind .byteArray (.leafMismatch 1 ⟨"payload", .byteArray, .required⟩))
#guard readFileRowGroup { column := { maxRows := 11 } } v2 ordinal payload 1 =
  .error (.int32 (.column 1 0 "ordinal" (.rowLimit 11 12)))

end Silmaril.Formats.Parquet.Int32ByteArrayGroup
