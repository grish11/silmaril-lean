module

import Silmaril.Formats.Parquet.DictionaryIndex.Thms
meta import Silmaril.Formats.Bytes

/-! Independent PyArrow dictionary data pages and invalid index streams. -/

namespace Silmaril.Formats.Parquet.DictionaryIndex

set_option maxRecDepth 4096

private def pageLimits : ScalarPage.Limits := ⟨32, 32, ⟨18, 6⟩, 0⟩
private def indexLimits : Hybrid.Limits := ⟨18, 8⟩
private def params (size count : Nat) (version : ScalarPage.Version) : ScalarPage.Parameters :=
  ⟨⟨size, size⟩, ⟨0, 1⟩, count, 0, 8, version⟩

private def mixedDictionaryBytes : Bytes := .ofList [19, 0, 0, 0, 0xfc, 0xff, 0xff, 0xff, 7, 0, 0, 0]
private def repeatedDictionaryBytes : Bytes := .ofList [0xfc, 0xff, 0xff, 0xff]
private def mixedDictionary : Array Int32 := #[19, -4, 7]
private def repeatedDictionary : Array Int32 := #[-4]
private def emptyDictionary : Array Int32 := #[]
private def mixedIndices : Bytes := .ofList [2, 3, 0x84, 0x09]
private def repeatedIndices : Bytes := .ofList [1, 0x20, 0]
private def nullIndices : Bytes := .ofList [0]

private def mixedV2 : Bytes := (.ofList [5, 0xed, 1] : Bytes).append mixedIndices
private def repeatedV2 : Bytes := (.ofList [3, 0xfe, 0x12, 1, 2, 0] : Bytes).append repeatedIndices
private def nullV2 : Bytes := (.ofList [6, 0] : Bytes).append nullIndices
private def mixedV1 : Bytes := (.ofList [3, 0, 0, 0] : Bytes).append mixedV2
private def repeatedV1 : Bytes := (.ofList [6, 0, 0, 0] : Bytes).append repeatedV2
private def nullV1 : Bytes := (.ofList [2, 0, 0, 0] : Bytes).append nullV2

private def mixed : List (Option Int32) :=
  [some 19, none, some (-4), some 19, none, some 7, some (-4), some 7, some 19]
private def repeated : List (Option Int32) := [none] ++ List.replicate 16 (some (-4)) ++ [none]

private def hex (bytes : Bytes) : String :=
  if bytes.length = 0 then "-" else
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (version name : String) (count nulls levels entries : Nat)
    (dictionary body indices : Bytes) : String :=
  String.intercalate "\t" [version, name, toString count, toString nulls, toString levels,
    "8", toString entries, hex dictionary, hex body, hex indices] ++ "\n"

#guard
    (include_str "../../../../tests/formats/parquet-dictionary-index/pyarrow-26.0.1.tsv") =
      fixtureLine "1.0" "mixed" 9 2 3 3 mixedDictionaryBytes mixedV1 mixedIndices ++
      fixtureLine "1.0" "repeat" 18 2 6 1 repeatedDictionaryBytes repeatedV1 repeatedIndices ++
      fixtureLine "1.0" "all-null" 3 3 2 0 .empty nullV1 nullIndices ++
      fixtureLine "2.0" "mixed" 9 2 3 3 mixedDictionaryBytes mixedV2 mixedIndices ++
      fixtureLine "2.0" "repeat" 18 2 6 1 repeatedDictionaryBytes repeatedV2 repeatedIndices ++
      fixtureLine "2.0" "all-null" 3 3 2 0 .empty nullV2 nullIndices

-- The fixture dictionary bodies can separately be read with the PLAIN INT32 API.
example : Plain.decodeInt32 3 mixedDictionaryBytes = .ok mixedDictionary.toList := rfl
example : Plain.decodeInt32 1 repeatedDictionaryBytes = .ok repeatedDictionary.toList := rfl
example : Plain.decodeInt32 0 .empty = .ok emptyDictionary.toList := rfl
example : readIndices indexLimits 7 mixedIndices = .ok [0, 1, 0, 2, 1, 2, 0] := rfl
example : readIndices indexLimits 16 repeatedIndices = .ok (List.replicate 16 0) := rfl
example : readIndices indexLimits 0 nullIndices = .ok [] := rfl

example : decode mixedDictionary (params 11 9 (.v1 3 3)) pageLimits indexLimits mixedV1 = .ok mixed := rfl
example : decode mixedDictionary (params 7 9 (.v2 2 9 0 3 (some false)))
    pageLimits indexLimits mixedV2 = .ok mixed := rfl
example : decode repeatedDictionary (params 13 18 (.v1 3 3))
    pageLimits indexLimits repeatedV1 = .ok repeated := rfl
example : decode repeatedDictionary (params 9 18 (.v2 2 18 0 6 (some false)))
    pageLimits indexLimits repeatedV2 = .ok repeated := rfl
example : decode emptyDictionary (params 7 3 (.v1 3 3))
    pageLimits indexLimits nullV1 = .ok [none, none, none] := rfl
example : decode emptyDictionary (params 3 3 (.v2 3 3 0 2 (some false)))
    pageLimits indexLimits nullV2 = .ok [none, none, none] := rfl

-- The deprecated tag uses the same index bytes once typed entries are supplied.
example : decode mixedDictionary { (params 11 9 (.v1 3 3)) with encoding := 2 }
    pageLimits indexLimits mixedV1 = .ok mixed := rfl
example : decode mixedDictionary { (params 7 9 (.v2 2 9 0 3 none)) with encoding := 2 }
    pageLimits indexLimits mixedV2 = .ok mixed := rfl

example : readIndices indexLimits 3 (.ofList [0, 6]) = .ok [0, 0, 0] := rfl
example : decode repeatedDictionary { (params 2 3 (.v1 3 3)) with schema := ⟨0, 0⟩ }
    pageLimits indexLimits (.ofList [0, 6]) = .ok (List.replicate 3 (some (-4))) := rfl
example : readIndices indexLimits 1 (.ofList [32, 2, 0xff, 0xff, 0xff, 0xff]) =
    .ok [4294967295] := rfl
example : readIndices indexLimits 0 .empty = .error .missingBitWidth := rfl
example : readIndices indexLimits 0 (.ofList [33]) = .error (.hybrid .invalidWidth) := rfl
example : readIndices ⟨18, 3⟩ 7 mixedIndices = .error .indexByteLimit := rfl
example : readIndices ⟨6, 8⟩ 7 mixedIndices = .error (.hybrid .valueLimit) := rfl
example : readIndices indexLimits 16 (.ofList [1, 0x20]) = .error (.hybrid .truncated) := rfl
example : readIndices indexLimits 7 (.ofList [2, 3, 0x84]) = .error (.hybrid .truncated) := rfl
example : readIndices indexLimits 15 repeatedIndices = .error (.hybrid .countMismatch) := rfl
example : readIndices indexLimits 7 (mixedIndices.push 0) = .error (.hybrid .trailingBytes) := rfl
example : readIndices indexLimits 1 (.ofList [1, 0x82, 0, 0]) =
    .error (.hybrid .noncanonicalHeader) := rfl
example : select emptyDictionary [0] = .error (.outOfBounds 0) := rfl

example : decode (#[19, -4] : Array Int32) (params 11 9 (.v1 3 3))
    pageLimits indexLimits mixedV1 = .error (.outOfBounds 2) := rfl
example : decode mixedDictionary (params 7 9 (.v2 1 9 0 3 (some false)))
    pageLimits indexLimits mixedV2 = .error (.page (.levels .presentCountMismatch)) := rfl
example : decode mixedDictionary (params 7 9 (.v2 2 9 0 3 (some false)))
    pageLimits indexLimits (mixedV2.push 0) = .error (.page (.payload .compressedSizeMismatch)) := rfl
example : decode mixedDictionary (params 8 9 (.v2 2 9 0 3 (some false)))
    pageLimits indexLimits (mixedV2.push 0) = .error (.hybrid .trailingBytes) := rfl
example : decode mixedDictionary { (params 11 9 (.v1 3 3)) with encoding := 0 }
    pageLimits indexLimits mixedV1 = .error (.unsupportedEncoding 0) := rfl

end Silmaril.Formats.Parquet.DictionaryIndex
