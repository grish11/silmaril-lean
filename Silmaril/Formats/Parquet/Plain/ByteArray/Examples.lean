module

import Silmaril.Formats.Parquet.Plain.ByteArray.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
meta import Silmaril.Formats.Bytes

/-! Exact PLAIN BYTE_ARRAY examples and independent PyArrow page fixtures. -/

namespace Silmaril.Formats.Parquet.Plain.ByteArray

set_option maxRecDepth 4096

private def limits : Limits := ⟨23, 3⟩
private def nonAscii : Bytes := .ofList [0xc3, 0xa9]
private def arbitraryBytes : Bytes := .ofList [0xff, 0x00, 0x80]
private def xy : Bytes := .ofList [0x78, 0x79]
private def present : List Bytes := [.empty, nonAscii, arbitraryBytes, xy]
private def slots : List (Option Bytes) :=
  [some .empty, none, some nonAscii, some arbitraryBytes, none, some xy]
private def scalars : Bytes := .ofList [
  0, 0, 0, 0, 2, 0, 0, 0, 0xc3, 0xa9, 3, 0, 0, 0, 0xff, 0x00, 0x80,
  2, 0, 0, 0, 0x78, 0x79]

private def mixedV1 : Bytes := (.ofList [2, 0, 0, 0, 3, 0x2d] : Bytes).append scalars
private def nullV1 : Bytes := .ofList [2, 0, 0, 0, 6, 0]
private def mixedV2 : Bytes := (.ofList [3, 0x2d] : Bytes).append scalars
private def nullV2 : Bytes := .ofList [6, 0]

private def hex (bytes : Bytes) : String :=
  if bytes.length = 0 then "-" else
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (version name : String) (count nulls definitionBytes : Nat)
    (body scalars : Bytes) : String :=
  String.intercalate "\t" [version, name, toString count, toString nulls, toString definitionBytes,
    hex body, hex scalars] ++ "\n"

#guard
    (include_str "../../../../../tests/formats/parquet-plain-byte-array/pyarrow-26.0.1.tsv") =
      fixtureLine "1.0" "mixed" 6 2 2 mixedV1 scalars ++
      fixtureLine "1.0" "all-null" 3 3 2 nullV1 .empty ++
      fixtureLine "2.0" "mixed" 6 2 2 mixedV2 scalars ++
      fixtureLine "2.0" "all-null" 3 3 2 nullV2 .empty

example : encode limits present = .ok scalars := rfl
example : decode limits 4 scalars = .ok present := rfl
example : decode ⟨0, 0⟩ 0 .empty = .ok [] := rfl
example : decode ⟨4, 0⟩ 1 (.ofList [0, 0, 0, 0]) = .ok [.empty] := rfl
example : encode ⟨4, 0⟩ [.empty] = .ok (.ofList [0, 0, 0, 0]) := rfl

private def long : Bytes := .ofList (List.replicate 256 0xab)
private def longWire : Bytes := (.ofList [0, 1, 0, 0] : Bytes).append long
example : encode ⟨260, 256⟩ [long] = .ok longWire := rfl
example : decode ⟨260, 256⟩ 1 longWire = .ok [long] := rfl

example : decode ⟨22, 3⟩ 4 scalars = .error .totalByteLimit := rfl
example : encode ⟨22, 3⟩ present = .error .totalByteLimit := rfl
example : decode ⟨23, 2⟩ 4 scalars = .error .valueByteLimit := rfl
example : encode ⟨23, 2⟩ present = .error .valueByteLimit := rfl
example : decode ⟨4, 2 ^ 31⟩ 1 (.ofList [0, 0, 0, 0x80]) = .error .integerOverflow := rfl
example : decode limits 1 (.ofList [0, 0, 0]) = .error .truncated := rfl
example : decode limits 1 (.ofList [2, 0, 0, 0, 0xc3]) = .error .truncated := rfl
example : decode limits 3 scalars = .error .trailingBytes := rfl
example : decode limits 5 scalars = .error .truncated := rfl
example : decode ⟨4, 0⟩ 0 (.ofList [0, 0, 0, 0]) = .error .trailingBytes := rfl

private def pageLimits : ScalarPage.Limits := ⟨32, 32, ⟨6, 2⟩, 0⟩
private def pageParams (size count : Nat) (version : ScalarPage.Version) : ScalarPage.Parameters :=
  ⟨⟨size, size⟩, ⟨0, 1⟩, count, 0, 0, version⟩

example : ScalarPage.decode (.byteArray limits) (pageParams 29 6 (.v1 3 3))
    pageLimits mixedV1 = .ok slots := rfl
example : ScalarPage.decode (.byteArray limits) (pageParams 25 6 (.v2 2 6 0 2 (some false)))
    pageLimits mixedV2 = .ok slots := rfl
example : ScalarPage.decode (.byteArray ⟨0, 0⟩) (pageParams 6 3 (.v1 3 3))
    pageLimits nullV1 = .ok [none, none, none] := rfl
example : ScalarPage.decode (.byteArray ⟨0, 0⟩) (pageParams 2 3 (.v2 3 3 0 2 (some false)))
    pageLimits nullV2 = .ok [none, none, none] := rfl
example : ScalarPage.decode (.byteArray ⟨23, 2⟩) (pageParams 25 6 (.v2 2 6 0 2 (some false)))
    pageLimits mixedV2 = .error (.plain .valueByteLimit) := rfl
example : ScalarPage.decode (.byteArray ⟨24, 3⟩) (pageParams 26 6 (.v2 2 6 0 2 (some false)))
    pageLimits (mixedV2.push 0) = .error (.plain .trailingBytes) := rfl

end Silmaril.Formats.Parquet.Plain.ByteArray
