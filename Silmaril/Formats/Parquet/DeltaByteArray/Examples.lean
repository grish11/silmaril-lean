module

import Silmaril.Formats.Parquet.DeltaByteArray.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.DeltaByteArray.Defs
meta import Batteries.Data.Except

/-! Independent parquet-java scalar slices, exact boundaries, and rejected inputs. -/

namespace Silmaril.Formats.Parquet.DeltaByteArray

private def deltaLimits : DeltaBinaryPacked.Limits := ⟨512, 160, 128, 4, 2⟩
private def limits : Limits := ⟨deltaLimits, ⟨deltaLimits, 256, 130⟩, 130, 600⟩
private def textBytes (s : String) : Bytes := ⟨s.toUTF8⟩
private def empty : Bytes := .ofList [0x80, 1, 4, 0, 0, 0x80, 1, 4, 0, 0]
private def singleton : Bytes := .ofList [0x80, 1, 4, 1, 0, 0x80, 1, 4, 1, 0]
private def exampleWire : Bytes := .ofList (
  [0x80, 1, 4, 4, 0, 3, 3, 0, 0, 0, 0x44, 1] ++ List.replicate 10 0 ++
  [0x80, 1, 4, 4, 8, 3, 3, 0, 0, 0, 0x70] ++ List.replicate 11 0 ++
  (textBytes "axislebabbleyhood").toList)
private def opaqueWire : Bytes := .ofList (
  [0x80, 1, 4, 7, 0, 5, 3, 0, 0, 0, 0x2b, 0xb1, 2] ++ List.replicate 9 0 ++
  [0x80, 1, 4, 7, 0, 3, 3, 0, 0, 0, 0x45, 0xc4] ++ List.replicate 10 0 ++
  [0xff, 0, 0x80, 0x81, 0, 0xff, 0])
private def repeatedWire : Bytes := .ofList (
  [0x80, 1, 4, 4, 0, 1, 8, 0, 0, 0, 0x83, 0, 2] ++ List.replicate 29 0 ++
  [0x80, 1, 4, 4, 0x84, 2, 0x83, 2, 8, 0, 0, 0, 0, 0x83, 0x81] ++ List.replicate 29 0 ++
  List.replicate 130 0xab ++ [0xff])
private def blocksWire : Bytes := .ofList (
  [0x80, 1, 4, 0x8c, 1, 0, 1, 3, 2, 2, 2, 0x84, 0x20, 8] ++
  (List.replicate 3 [0x82, 0x20, 8]).flatten ++ List.replicate 24 0x22 ++
  [1, 2, 2, 2, 2] ++ List.replicate 8 0x22 ++
  [0x80, 1, 4, 0x8c, 1, 6, 5, 3, 3, 3, 3, 0xa0, 0x28, 0x8a] ++
  (List.replicate 15 [0xa2, 0x28, 0x8a]).flatten ++
  [1, 2, 3, 3, 3, 0x88, 0x88, 8] ++ List.replicate 5 0x22 ++
  [0xff, 0] ++ (List.range 70).map UInt8.ofNat)

private def hex (bytes : Bytes) : String :=
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def boundaries (count : Nat) (body : Bytes) : Option (Nat × Nat) := do
  let (prefixStream, tail) ← (DeltaBinaryPacked.parsePrefix .int32 deltaLimits count body).toOption
  let (suffixStream, _) ←
    (DeltaBinaryPacked.parsePrefix .int32 deltaLimits count (.ofList tail)).toOption
  pure (prefixStream.wire.length, prefixStream.wire.length + suffixStream.wire.length)

private def fixtureLine (name : String) (count : Nat) (body : Bytes) : String :=
  match boundaries count body with
  | some (prefixEnd, payloadStart) =>
    String.intercalate "\t" [name, toString count, toString prefixEnd, toString payloadStart, hex body] ++ "\n"
  | none => ""

#guard (include_str "../../../../tests/formats/parquet-delta-byte-array/parquet-java-1.16.0.tsv") =
  fixtureLine "empty" 0 empty ++ fixtureLine "singleton-empty" 1 singleton ++
  fixtureLine "spec" 4 exampleWire ++ fixtureLine "opaque" 7 opaqueWire ++
  fixtureLine "repeated" 4 repeatedWire ++ fixtureLine "blocks" 140 blocksWire

private def longValue : Bytes := .replicate 130 0xab
private def changedValue : Bytes := (.replicate 129 0xab : Bytes).push 0xff
private def repeatedValues : List Bytes := [longValue, longValue, changedValue, changedValue]
private def blocksValues : List Bytes := (List.range 140).map fun i =>
  .ofList [0xff, 0, UInt8.ofNat (i / 2)]

#guard decode limits 0 empty = .ok []
#guard decode limits 1 singleton = .ok [.empty]
#guard decode limits 4 exampleWire = .ok (["axis", "axle", "babble", "babyhood"].map textBytes)
#guard decode limits 7 opaqueWire = .ok [
  .empty, .ofList [0xff, 0, 0x80], .ofList [0xff, 0, 0x81], .ofList [0xff, 0, 0x81],
  .empty, .ofList [0, 0xff], .ofList [0, 0xff, 0]]
#guard decode limits 4 repeatedWire = .ok repeatedValues
#guard decode limits 140 blocksWire = .ok blocksValues

#guard decode limits 1 (.ofList [0x80, 1, 4, 1, 2, 0x80, 1, 4, 1, 0]) = .error .nonzeroFirstPrefix
#guard decode limits 2 (.ofList [0x80, 1, 4, 2, 0, 1, 0, 0, 0, 0, 0x80, 1, 4, 2, 0, 0, 0, 0, 0, 0]) =
  .error (.negativePrefix (-1))
#guard decode limits 2 (.ofList [0x80, 1, 4, 2, 0, 4, 0, 0, 0, 0, 0x80, 1, 4, 2, 0, 0, 0, 0, 0, 0]) =
  .error .prefixTooLong
#guard decode limits 1 (.ofList [0x80, 1, 4, 1, 0, 0x80, 1, 4, 1, 1]) =
  .error (.suffixStream (.negativeLength (-1)))
#guard decode limits 1 (.ofList [0x80, 1, 4, 1, 0, 0x80, 1, 4, 0, 0]) =
  .error (.suffixStream (.lengths .countMismatch))
#guard decode limits 1 (.ofList (singleton.toList.take 9)) =
  .error (.suffixStream (.lengths (.wire .truncated)))
#guard decode limits 7 (.ofList (opaqueWire.toList.take (opaqueWire.length - 1))) =
  .error (.suffixStream .truncated)
#guard decode limits 7 (opaqueWire.push 0) = .error (.suffixStream .trailingBytes)
#guard decode limits 0 (empty.push 0) = .error (.suffixStream .trailingBytes)
#guard decode limits 1 .empty = .error (.prefixStream (.wire .truncated))
#guard decode limits 0 singleton = .error (.prefixStream .countMismatch)
#guard reconstruct limits [0] [] = .error .countMismatch
#guard reconstruct limits [] [.empty] = .error .countMismatch
#guard decode { limits with prefixes := { deltaLimits with bytes := 9 } } 1 singleton =
  .error (.prefixStream .byteLimit)
#guard decode { limits with valueBytes := 7 } 4 exampleWire = .error .valueLimit
#guard decode { limits with decodedBytes := 519 } 4 repeatedWire = .error .decodedByteLimit
#guard decode { limits with decodedBytes := 520 } 4 repeatedWire = .ok repeatedValues
#guard Internal.checkSize (2 ^ 32) (2 ^ 32) (2 ^ 31 - 1) 1 = .error .valueOverflow
#guard Internal.checkSize (2 ^ 31 - 1) (2 ^ 31 - 1) (2 ^ 31 - 2) 1 = .ok ()

end Silmaril.Formats.Parquet.DeltaByteArray
