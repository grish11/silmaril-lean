module

import Silmaril.Formats.Parquet.ScalarPage.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.ScalarPage.Defs
meta import Batteries.Data.Except

/-! Independent PyArrow INT32 page bodies and rejected page parameters. -/

namespace Silmaril.Formats.Parquet.ScalarPage

set_option maxRecDepth 4096

private def limits : Limits := ⟨256, 256, ⟨80, 16⟩, 0⟩
private def v1 (codec : Int) (compressed uncompressed slots : Nat) : Parameters :=
  ⟨⟨compressed, uncompressed⟩, ⟨0, 1⟩, slots, codec, 0, .v1 3 3⟩
private def v2 (codec : Int) (compressed uncompressed slots nulls levelBytes : Nat)
    (flag : Option Bool) : Parameters :=
  ⟨⟨compressed, uncompressed⟩, ⟨0, 1⟩, slots, codec, 0, .v2 nulls slots 0 levelBytes flag⟩

private def scalarBytes : Bytes := .ofList [7, 0, 0, 0, 0xfc, 0xff, 0xff, 0xff, 19, 0, 0, 0]
private def rawV1 : Bytes := (.ofList [2, 0, 0, 0, 3, 0x15] : Bytes).append scalarBytes
private def snappyV1 : Bytes := (.ofList [0x12, 0x44] : Bytes).append rawV1
private def nullSnappyV1 : Bytes := .ofList [6, 0x14, 2, 0, 0, 0, 6, 0]
private def rawV2 : Bytes := (.ofList [3, 0x15] : Bytes).append scalarBytes
private def nullV2 : Bytes := .ofList [6, 0]
private def snappyV2 : Bytes := .ofList [
  0x15, 0xb5, 0xd6, 0x5a, 0x6b, 0xad, 0xb5, 0xd6, 0x5a, 0x6b, 0xad,
  0xc0, 0x01, 0x2c, 7, 0, 0, 0, 0xfc, 0xff, 0xff, 0xff, 19, 0, 0, 0,
  0xfe, 0x0c, 0, 0xfe, 0x0c, 0, 0xce, 0x0c, 0]
private def mixed : List (Option Int32) := [some 7, none, some (-4), none, some 19]

private def rawV1Params : Parameters := v1 0 18 18 5
private def snappyV1Params : Parameters := v1 1 20 18 5
private def nullSnappyV1Params : Parameters := v1 1 8 6 3
private def rawV2Params : Parameters := v2 0 14 14 5 2 2 (some false)
private def bypassV2Params : Parameters := v2 1 14 14 5 2 2 (some false)
private def nullV2Params : Parameters := v2 1 2 2 3 3 2 (some false)
private def snappyV2Params : Parameters := v2 1 35 203 80 32 11 (some true)

private def hex (bytes : Bytes) : String :=
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (compression name : String) (params : Parameters) (body : Bytes) : String :=
  let (version, versionFields) := match params.version with
    | .v1 _ _ => ("1.0", ["-", "-", "-", "-", "-"])
    | .v2 nulls rows rep defBytes flag =>
      let flagField := match flag with
        | none => "-"
        | some true => "1"
        | some false => "0"
      ("2.0", [toString nulls, toString rows, toString rep, toString defBytes, flagField])
  String.intercalate "\t" ([version, compression, name, toString params.codec,
    toString params.sizes.compressed, toString params.sizes.uncompressed, toString params.numValues] ++
    versionFields ++ [hex body]) ++ "\n"

#guard
    (include_str "../../../../tests/formats/parquet-scalar-page/pyarrow-26.0.1.tsv") =
      fixtureLine "NONE" "mixed" rawV1Params rawV1 ++
      fixtureLine "SNAPPY" "mixed" snappyV1Params snappyV1 ++
      fixtureLine "SNAPPY" "all-null" nullSnappyV1Params nullSnappyV1 ++
      fixtureLine "NONE" "mixed" rawV2Params rawV2 ++
      fixtureLine "SNAPPY" "mixed" bypassV2Params rawV2 ++
      fixtureLine "SNAPPY" "all-null" nullV2Params nullV2 ++
      fixtureLine "SNAPPY" "mixed-compressed" snappyV2Params snappyV2

example : decode .int32 rawV1Params limits rawV1 = .ok mixed := rfl
example : decode .int32 rawV2Params limits rawV2 = .ok mixed := rfl
example : decode .int32 bypassV2Params limits rawV2 = .ok mixed := rfl
example : decode .int32 nullV2Params limits nullV2 = .ok [none, none, none] := rfl

private def int32Page (params : Parameters) (bytes : Bytes) : Except Error (List (Option Int32)) :=
  decode .int32 params limits bytes

#guard int32Page snappyV1Params snappyV1 = .ok mixed
#guard int32Page nullSnappyV1Params nullSnappyV1 = .ok [none, none, none]
#guard int32Page snappyV2Params snappyV2 = .ok (List.replicate 16 mixed).flatten
#guard int32Page { snappyV2Params with version := .v2 32 80 0 11 none } snappyV2 =
    .ok (List.replicate 16 mixed).flatten
#guard int32Page { snappyV2Params with sizes := ⟨36, 203⟩ } (snappyV2.push 0) =
    .error (.payload (.trailingInput .snappy))

example : decode .int32 { rawV1Params with schema := ⟨0, 0⟩, numValues := 3, sizes := ⟨12, 12⟩ }
    limits scalarBytes = .ok ([some 7, some (-4), some 19] : List (Option Int32)) := rfl
example : decode .boolean { (v2 0 1 1 3 0 0 none) with schema := ⟨0, 0⟩ }
    limits (.ofList [0xfd]) = .ok [some true, some false, some true] := rfl

example : decode .int32 { rawV1Params with encoding := 8 } limits rawV1 =
    .error (.unsupportedEncoding 8) := rfl
example : decode .int32 { rawV1Params with version := .v1 4 3 } limits rawV1 =
    .error .unsupportedLevelEncoding := rfl
example : decode .int32 { rawV1Params with version := .v1 3 4 } limits rawV1 =
    .error .unsupportedLevelEncoding := rfl
example : decode .int32 { rawV1Params with sizes := ⟨18, 2 ^ 31⟩ } limits rawV1 =
    .error .invalidPageSize := rfl
example : decode .int32 rawV1Params { limits with compressedBytes := 17 } rawV1 =
    .error (.payload .compressedLimit) := rfl
example : decode .int32 snappyV2Params { limits with uncompressedBytes := 202 } snappyV2 =
    .error (.payload .outputLimit) := rfl
example : decode .int32 rawV1Params limits (rawV1.push 0) =
    .error (.payload .compressedSizeMismatch) := rfl
example : decode .int32 (v1 0 19 19 5) limits (rawV1.push 0) =
    .error (.plain .trailingBytes) := rfl
example : decode .int32 (v1 0 17 17 5) limits (.ofList (rawV1.toList.take 17)) =
    .error (.plain .truncated) := rfl
example : prepare (v2 0 1 2 1 0 2 none) limits (.ofList [3]) =
    .error .invalidLevelExtent := rfl
example : prepare (v2 0 2 1 1 0 2 none) limits (.ofList [3, 1]) =
    .error .invalidLevelExtent := rfl
example : prepare { rawV2Params with version := .v2 6 5 0 2 (some false) } limits rawV2 =
    .error .invalidNullCount := rfl
example : prepare { rawV2Params with version := .v2 2 4 0 2 (some false) } limits rawV2 =
    .error .invalidRowCount := rfl
example : prepare { rawV2Params with version := .v2 2 5 1 2 (some false) } limits rawV2 =
    .error (.levels .unexpectedRepetitionSection) := rfl
example : prepare { rawV2Params with version := .v2 1 5 0 2 (some false) } limits rawV2 =
    .error (.levels .presentCountMismatch) := rfl
example : prepare (v2 0 3 3 5 2 3 (some false)) limits (.ofList [3, 0x15, 0]) =
    .error (.levels (.hybrid .trailingBytes)) := rfl
example : prepare { snappyV2Params with version := .v2 32 80 0 11 (some false) } limits snappyV2 =
    .error (.payload .outputSizeMismatch) := rfl

end Silmaril.Formats.Parquet.ScalarPage
