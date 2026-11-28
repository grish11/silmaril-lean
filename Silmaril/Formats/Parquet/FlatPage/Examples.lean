module

import Silmaril.Formats.Parquet.FlatPage.Thms
meta import Silmaril.Formats.Bytes

/-! PyArrow 26.0.1 V1/V2 fixtures, with an exact INT32 test decoder. -/

namespace Silmaril.Formats.Parquet.FlatPage

set_option maxRecDepth 4096

private def required : LevelSchema := ⟨0, 0⟩
private def optional : LevelSchema := ⟨0, 1⟩
private def limits : Hybrid.Limits := ⟨8, 16⟩
private def scalarBytes : Bytes := .ofList [7, 0, 0, 0, 0xfc, 0xff, 0xff, 0xff, 19, 0, 0, 0]
private def mixedV1 : Bytes := .ofList [2, 0, 0, 0, 3, 0x15]
private def mixedV2 : Bytes := .ofList [3, 0x15]
private def nullV1 : Bytes := .ofList [2, 0, 0, 0, 6, 0]
private def nullV2 : Bytes := .ofList [6, 0]

-- The test callback stands in for a physical decoder at the explicit scalar seam.
private def int32Reader (count : Nat) (source : Bytes) : Except Unit (List Int32) :=
  if source.length = 4 * count then
    let octets := source.toList
    .ok (List.ofFn fun i : Fin count =>
      (UInt32.ofNat (KBytes.leVal ((octets.drop (4 * i.val)).take 4))).toInt32)
  else .error ()

private def hex (bytes : Bytes) : String :=
  if bytes.length = 0 then "-" else
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (version name : String) (slots present declared : Nat)
    (definitions scalars : Bytes) : String :=
  version ++ "\t" ++ name ++ "\t" ++ toString slots ++ "\t" ++ toString present ++ "\t" ++
    toString declared ++ "\t" ++ hex definitions ++ "\t" ++ hex scalars ++ "\n"

#guard
    (include_str "../../../../tests/formats/parquet-flat-page/pyarrow-26.0.1.tsv") =
      fixtureLine "1.0" "required" 3 3 0 .empty scalarBytes ++
      fixtureLine "1.0" "mixed-null" 5 3 2 mixedV1 scalarBytes ++
      fixtureLine "1.0" "all-null" 3 0 2 nullV1 .empty ++
      fixtureLine "2.0" "required" 3 3 0 .empty scalarBytes ++
      fixtureLine "2.0" "mixed-null" 5 3 2 mixedV2 scalarBytes ++
      fixtureLine "2.0" "all-null" 3 0 2 nullV2 .empty

example : decode required 3 3 limits (.v1 scalarBytes) int32Reader =
    .ok [some 7, some (-4), some 19] := rfl
example : decode optional 5 3 limits (.v1 (mixedV1.append scalarBytes)) int32Reader =
    .ok [some 7, none, some (-4), none, some 19] := rfl
example : decode optional 3 0 limits (.v1 nullV1) int32Reader = .ok [none, none, none] := rfl
example : decode required 3 3 limits (.v2 0 0 .empty scalarBytes) int32Reader =
    .ok [some 7, some (-4), some 19] := rfl
example : decode optional 5 3 limits (.v2 0 2 mixedV2 scalarBytes) int32Reader =
    .ok [some 7, none, some (-4), none, some 19] := rfl
example : decode optional 3 0 limits (.v2 0 2 nullV2 .empty) int32Reader =
    .ok [none, none, none] := rfl

example : splitV1Optional 16 (mixedV1.append scalarBytes) =
    .ok ⟨mixedV2, scalarBytes⟩ := rfl
example : splitV1Optional 16 (.ofList [2, 0, 0]) =
    .error .truncatedDefinitionLength := rfl
example : splitV1Optional 16 (.ofList [2, 0, 0, 0, 3]) =
    .error .truncatedDefinitions := rfl
example : splitV1Optional 1 (mixedV1.append scalarBytes) =
    .error .definitionByteLimit := rfl
example : splitV1Optional 16 (.ofList [0, 1, 0, 0]) =
    .error .definitionByteLimit := rfl

example : plan ⟨1, 1⟩ 5 3 limits (.v2 0 2 mixedV2 scalarBytes) =
    .error .unsupportedLevels := rfl
example : plan ⟨0, 2⟩ 5 3 limits (.v2 0 2 mixedV2 scalarBytes) =
    .error .unsupportedLevels := rfl
example : plan optional 5 3 limits (.v2 1 2 mixedV2 scalarBytes) =
    .error .unexpectedRepetitionSection := rfl
example : plan optional 5 3 limits (.v2 0 1 mixedV2 scalarBytes) =
    .error .invalidDefinitionLength := rfl
example : plan optional 5 3 ⟨8, 1⟩ (.v2 0 2 mixedV2 scalarBytes) =
    .error .definitionByteLimit := rfl
example : plan required 5 3 limits (.v2 0 2 mixedV2 scalarBytes) =
    .error .unexpectedDefinitionSection := rfl
example : plan optional 9 3 limits (.v2 0 2 mixedV2 scalarBytes) = .error .countLimit := rfl
example : plan optional 5 2 limits (.v2 0 2 mixedV2 scalarBytes) =
    .error .presentCountMismatch := rfl
example : plan optional 2 3 limits (.v2 0 2 mixedV2 scalarBytes) =
    .error .presentCountMismatch := rfl
example : plan optional 5 3 limits (.v2 0 3 (mixedV2.push 0) scalarBytes) =
    .error (.hybrid .trailingBytes) := rfl
example : plan optional 5 3 limits (.v2 0 1 (.ofList [3]) scalarBytes) =
    .error (.hybrid .truncated) := rfl

example : decode optional 5 3 limits (.v2 0 2 mixedV2 scalarBytes)
    (fun _ _ => .ok ([7, -4] : List Int32) : Nat → Bytes → Except Unit (List Int32)) =
    .error (.page .scalarCountMismatch) := rfl
example : decode optional 5 3 limits (.v2 0 2 mixedV2 scalarBytes)
    (fun _ _ => .ok ([7, -4, 19, 6] : List Int32) : Nat → Bytes → Except Unit (List Int32)) =
    .error (.page .scalarCountMismatch) := rfl
example : decode optional 5 3 limits (.v2 0 2 mixedV2 (scalarBytes.push 0)) int32Reader =
    .error (.scalar ()) := rfl
example : decode optional 0 0 limits (.v1 (.ofList [0, 0, 0, 0])) int32Reader = .ok [] := rfl
example : decode optional 0 0 limits (.v2 0 0 .empty .empty) int32Reader = .ok [] := rfl

end Silmaril.Formats.Parquet.FlatPage
