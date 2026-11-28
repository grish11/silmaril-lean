module

import Silmaril.Formats.Parquet.DeltaLengthByteArray.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.DeltaLengthByteArray.Defs
meta import Batteries.Data.Except

/-! Pinned parquet-java scalar slices and malformed length and extent cases. -/

namespace Silmaril.Formats.Parquet.DeltaLengthByteArray

private def limits : Limits := ⟨⟨512, 160, 128, 4, 2⟩, 160, 130⟩
private def emptyHeader : Bytes := .ofList [0x80, 1, 4, 0, 0]
private def singletonHeader : Bytes := .ofList [0x80, 1, 4, 1, 0]
private def mixedHeader : Bytes := .ofList ([0x80, 1, 4, 5, 2, 3, 3, 0, 0, 0, 0xe1] ++
  List.replicate 11 0)
private def mixedPayload : Bytes := .ofList [0x61, 0xc3, 0xa9, 0xff, 0, 0x80, 0]
private def mixedValues : List Bytes :=
  [.ofList [0x61], .empty, .ofList [0xc3, 0xa9], .ofList [0xff, 0, 0x80], .ofList [0]]
private def longHeader : Bytes := .ofList ([0x80, 1, 4, 3, 0x84, 2, 0x83, 2, 8, 0, 0, 0, 0, 0x84] ++
  List.replicate 30 0)
private def longValue : Bytes := .replicate 130 0xab
private def longPayload : Bytes := longValue.append (.ofList [0x7f, 0])
private def blocksHeader : Bytes := .ofList ([0x80, 1, 4, 0x8c, 1, 2, 1, 2, 2, 2, 2] ++
  List.replicate 32 0x94 ++ [1, 2, 2, 2, 2] ++ List.replicate 8 0x94)
private def blocksPayload : Bytes := .ofList ((List.range 35).map fun i => UInt8.ofNat (i * 4))
private def blocksValues : List Bytes := (List.range 140).map fun i =>
  if i % 4 = 0 then .ofList [UInt8.ofNat i] else .empty

private def hex (bytes : Bytes) : String :=
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (name : String) (count : Nat) (header payload : Bytes) : String :=
  String.intercalate "\t" [name, toString count, toString header.length, hex (header.append payload)] ++ "\n"

#guard
    (include_str "../../../../tests/formats/parquet-delta-length-byte-array/parquet-java-1.16.0.tsv") =
      fixtureLine "empty" 0 emptyHeader .empty ++
      fixtureLine "singleton-empty" 1 singletonHeader .empty ++
      fixtureLine "mixed" 5 mixedHeader mixedPayload ++
      fixtureLine "long" 3 longHeader longPayload ++
      fixtureLine "blocks" 140 blocksHeader blocksPayload

#guard decode limits 0 emptyHeader = .ok []
#guard decode limits 1 singletonHeader = .ok [.empty]
#guard decode limits 5 (mixedHeader.append mixedPayload) = .ok mixedValues
#guard decode limits 3 (longHeader.append longPayload) = .ok [longValue, .empty, .ofList [0x7f, 0]]
#guard decode limits 140 (blocksHeader.append blocksPayload) = .ok blocksValues

private def prefixResult (count : Nat) (source : Bytes) :
    Except DeltaBinaryPacked.Error (Nat × List Int32 × List UInt8) :=
  (DeltaBinaryPacked.parsePrefix .int32 limits.lengths count source).map fun (stream, payload) =>
    (stream.wire.length, stream.reconstruct .int32, payload)

#guard prefixResult 0 emptyHeader = .ok (5, [], [])
#guard prefixResult 1 singletonHeader = .ok (5, [0], [])
#guard prefixResult 5 (mixedHeader.append mixedPayload) = .ok (22, [1, 0, 2, 3, 1], mixedPayload.toList)
#guard prefixResult 3 (longHeader.append longPayload) = .ok (44, [130, 0, 2], longPayload.toList)
#guard prefixResult 140 (blocksHeader.append blocksPayload) =
  .ok (56, blocksValues.map (fun value => Int32.ofNat value.length), blocksPayload.toList)
#guard DeltaBinaryPacked.decode .int32 limits.lengths 5 (mixedHeader.append mixedPayload) =
  .error .trailingBytes
#guard DeltaBinaryPacked.decode .int32 limits.lengths 5 mixedHeader = .ok [1, 0, 2, 3, 1]

#guard decode limits 1 (.ofList [0x80, 1, 4, 1, 1]) = .error (.negativeLength (-1))
#guard decode limits 2 (.ofList [0x80, 1, 4, 2, 0, 1, 0, 0, 0, 0]) = .error (.negativeLength (-1))
#guard decode limits 5 (mixedHeader.append (.ofList (mixedPayload.toList.take 6))) = .error .truncated
#guard decode limits 5 (mixedHeader.append (mixedPayload.push 0)) = .error .trailingBytes
#guard decode limits 0 (emptyHeader.push 0) = .error .trailingBytes
#guard decode limits 1 (singletonHeader.push 0) = .error .trailingBytes
#guard decode limits 1 (.ofList [0x80, 1, 4, 1]) = .error (.lengths (.wire .truncated))
#guard decode limits 4 (mixedHeader.append mixedPayload) = .error (.lengths .countMismatch)
#guard decode { limits with valueBytes := 2 } 5 (mixedHeader.append mixedPayload) = .error .valueLimit
#guard decode { limits with payloadBytes := 6 } 5 (mixedHeader.append mixedPayload) = .error .payloadLimit
#guard decode { limits with lengths := { limits.lengths with bytes := 22 } } 5
    (mixedHeader.append mixedPayload) = .error (.lengths .byteLimit)
#guard decode { limits with lengths := { limits.lengths with blocks := 1 } } 140
    (blocksHeader.append blocksPayload) = .error (.lengths .blockLimit)
#guard assemble { limits with valueBytes := 2147483647 } [2147483647] [] = .error .truncated

end Silmaril.Formats.Parquet.DeltaLengthByteArray
