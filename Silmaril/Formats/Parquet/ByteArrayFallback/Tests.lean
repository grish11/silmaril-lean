module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Defs

/-! PyArrow V1 and V2 fallback, plus three original indexed failures. -/

namespace Silmaril.Formats.Parquet.ByteArrayFallback

private def v1 : Bytes :=
  ⟨include_bytes "../../../../data/parquet-byte-array-fallback/byte-array-fallback-v1.parquet"⟩
private def v2 : Bytes :=
  ⟨include_bytes "../../../../data/parquet-byte-array-fallback/byte-array-fallback-v2.parquet"⟩
private def missingDictionary : Bytes :=
  ⟨include_bytes "../../../../data/parquet-byte-array-fallback/byte-array-fallback-v2-missing-dictionary.parquet"⟩
private def badTag : Bytes :=
  ⟨include_bytes "../../../../data/parquet-byte-array-fallback/byte-array-fallback-v2-bad-tag.parquet"⟩
private def badLength : Bytes :=
  ⟨include_bytes "../../../../data/parquet-byte-array-fallback/byte-array-fallback-v2-bad-length.parquet"⟩

private def plainV1 : Bytes :=
  ⟨include_bytes "../../../../data/parquet-plain-byte-array-file/plain-byte-array-v1.parquet"⟩

private def expectedSlot (group row : Nat) : Option Bytes :=
  if row % 13 == 5 then none else
    let valueBytes := if row < 256 then
      if row % 2 == 0 then [0, 255] else []
    else
      let digits := toString row
      let sized := String.ofList (List.replicate (4 - digits.length) '0' ++ digits.toList)
      ("distinct-" ++ sized ++ "-").toUTF8.data.toList ++
        (List.replicate 4 ("opaque-value-".toUTF8.data.toList ++ [255])).flatten
    some (Bytes.ofList (valueBytes ++ [group.toUInt8]))

private def expected (group : Nat) : List (Option Bytes) :=
  (List.range 384).map (expectedSlot group)

private def bindFixture (input : Bytes) : IO (Checked "payload") := do
  let .ok checked := openFile {} input "payload" | throw (IO.userError "expected checked selection")
  unless checked.binding.leafOrdinal == 2 && checked.binding.columnOrdinal == 1 &&
      checked.snapshot.groupCount == 2 do
    throw (IO.userError "wrong original leaf, column or footer group")
  return checked

private def clean (version : String) (input : Bytes) : IO Unit := do
  let checked ← bindFixture input
  unless readGroup checked {} 0 == .ok (expected 0) && readGroup checked {} 1 == .ok (expected 1) do
    throw (IO.userError "wrong exact mixed slots or dictionary state leaked across chunks")
  let .error (.column 0 1 "payload" .encodings) := Plain.ByteArray.File.Checked.readGroup checked {} 0 |
    throw (IO.userError "the original PLAIN reader admitted mixed metadata")
  IO.println s!"{version}: two checked groups and 768 exact opaque slots across dictionary fallback"

#eval clean "V1" v1
#eval clean "V2" v2

#eval do
  let .ok checked := openFile {} plainV1 "payload" | throw (IO.userError "expected a checked PLAIN file")
  let .ok slots := Plain.ByteArray.File.Checked.readGroup checked {} 0 |
    throw (IO.userError "expected the original PLAIN group")
  let .ok fallback := readGroup checked {} 0 | throw (IO.userError "expected an admitted all-PLAIN chunk")
  unless fallback == slots do throw (IO.userError "the all-PLAIN chunk differs without a dictionary")
  IO.println "All-PLAIN control: exact slots without a leading dictionary"

private def damaged (input : Bytes) (page offset : Nat) (reason : FlatColumn.PageError DecodeError) : IO Unit := do
  let checked ← bindFixture input
  unless readGroup checked {} 0 == .ok (expected 0) do
    throw (IO.userError "the unaffected original group differs")
  let .error actual := readGroup checked {} 1 | throw (IO.userError "damaged group produced rows")
  unless actual == .page 1 1 "payload" page offset reason do
    throw (IO.userError s!"wrong original page failure: {reprStr actual}")
  IO.println s!"V2 control: group 1, column 1, page {page}, header {offset}: {reprStr reason}"

#eval damaged missingDictionary 0 15111 (.decode .missingDictionary)
#eval damaged badTag 19 16814 (.encoding 3)
#eval damaged badLength 24 22513 (.decode (.plain (.plain .integerOverflow)))

#eval do
  let checked ← bindFixture v2
  let .error (.page 0 1 "payload" 0 2164 (.decode (.dictionaryEntryLimit 0 _))) :=
    readGroup checked { maxDictionaryEntries := 0 } 0 |
    throw (IO.userError "dictionary entry cap did not precede materialization")
  let .error (.page 0 1 "payload" 0 2164 .byteLimit) :=
    readGroup checked { maxDictionaryBytes := 0 } 0 |
    throw (IO.userError "dictionary byte cap did not precede materialization")

end Silmaril.Formats.Parquet.ByteArrayFallback
