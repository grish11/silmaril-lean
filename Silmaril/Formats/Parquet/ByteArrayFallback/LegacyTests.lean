module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Defs

/-! A parquet-java 1.16.0 V1 tag-2 to tag-0 transition in one BYTE_ARRAY chunk. -/

namespace Silmaril.Formats.Parquet.ByteArrayFallback

private def clean : Bytes :=
  ⟨include_bytes "../../../../data/parquet-byte-array-legacy-fallback/parquet-java-v1-legacy-fallback.parquet"⟩

private def damaged : Bytes :=
  ⟨include_bytes "../../../../data/parquet-byte-array-legacy-fallback/parquet-java-v1-legacy-fallback-bad-length.parquet"⟩

private def expectedSlot (row : Nat) : Option Bytes :=
  if row % 13 == 5 then none
  else
    let digits := toString row
    let padded := String.ofList (List.replicate (4 - digits.length) '0' ++ digits.toList)
    let value := if row < 256 then
      if row % 2 == 0 then "repeat-a" else "repeat-b"
    else "distinct-" ++ padded ++ "-" ++ String.join (List.replicate 4 "opaque-value-")
    some ⟨value.toUTF8⟩

#eval do
  let .ok checked := openFile {} clean "payload" | throw (IO.userError "legacy footer or selection rejected")
  unless checked.binding.columnOrdinal == 1 && checked.binding.leafOrdinal == 2 do
    throw (IO.userError "wrong original leaf or column")
  let .ok slots := readLegacyGroup checked {} 0 | throw (IO.userError "legacy fallback rejected")
  unless slots == (List.range 384).map expectedSlot do throw (IO.userError "wrong legacy slots")
  let .error (.column 0 1 "payload" .encodings) := readGroup checked {} 0 |
    throw (IO.userError "the tag-8 profile admitted legacy metadata")
  let .error (.column 0 1 "payload" .encodings) := Plain.ByteArray.File.Checked.readGroup checked {} 0 |
    throw (IO.userError "the PLAIN profile admitted legacy metadata")
  IO.println "parquet-java V1: 384 exact slots across ten tag-2 and nine PLAIN data frames"

#eval do
  let .ok checked := openFile {} damaged "payload" | throw (IO.userError "damaged fixture footer rejected")
  let .error (.page 0 1 "payload" 19 10089 (.decode (.plain (.plain .integerOverflow)))) :=
    readLegacyGroup checked {} 0 | throw (IO.userError "expected original final-frame length rejection")
  IO.println "Damaged legacy fallback: group 0, column 1, frame 19, header 10089, integerOverflow"

#guard clean.data[10116]! == 66
#guard damaged.data == (((clean.data.set! 10116 255).set! 10117 255).set! 10118 255).set! 10119 255

#guard clean.data[1910]! == 4 && clean.data[1948]! == 4 && clean.data[1950]! == 6

#eval do
  let check (offset : Nat) (byte : UInt8) (frame header : Nat)
      (reason : FlatColumn.PageError DecodeError) : IO Unit := do
    let .ok checked := openFile {} ⟨clean.data.set! offset byte⟩ "payload" |
      throw (IO.userError "header control failed before group read")
    let .error failure := readLegacyGroup checked {} 0 |
      throw (IO.userError "legacy profile admitted an unsupported header")
    unless decide (failure = FlatColumn.Error.page 0 1 "payload" frame header reason) do
      throw (IO.userError s!"wrong legacy header failure: {reprStr failure}")
  check 1910 0 0 1900 (.decode (.dictionaryEncoding 0))
  check 1948 16 1 1937 (.encoding 8)
  check 1950 8 1 1937 .levels
  IO.println "Legacy header controls preserve original dictionary, value-tag, and definition-tag failures"

end Silmaril.Formats.Parquet.ByteArrayFallback
