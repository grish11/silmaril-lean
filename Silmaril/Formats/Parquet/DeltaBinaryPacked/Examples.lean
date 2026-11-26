module

import Silmaril.Formats.Parquet.DeltaBinaryPacked.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.DeltaBinaryPacked.Defs
meta import Batteries.Data.Except

/-! Independent parquet-java scalar streams and checked rejection cases. -/

namespace Silmaril.Formats.Parquet.DeltaBinaryPacked

private def limits : Limits := ⟨512, 256, 256, 16, 2⟩
private def empty32 : Bytes := .ofList [0x80, 1, 4, 0, 0]
private def singleton32 : Bytes := .ofList [0x80, 1, 4, 1, 0xff, 0xff, 0xff, 0xff, 0x0f]
private def wrap32 : Bytes := .ofList ([
  0x80, 1, 4, 7, 0, 0xff, 0xff, 0xff, 0xff, 0x0f, 32, 0, 0, 0,
  0, 0, 0, 0, 0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0, 1] ++ List.replicate 115 0)
private def blocks32 : Bytes := .ofList [
  0x80, 1, 4, 0x8c, 1, 0xd0, 0x0f, 0x0d, 3, 3, 3, 3,
  0x6d, 0x8b, 0xb6, 0x45, 0xdb, 0xa2, 0x6d, 0xd1, 0xb6, 0x68, 0x5b, 0xb4, 0x2d, 0xda, 0x16,
  0x6d, 0x8b, 0xb6, 0x45, 0xdb, 0xa2, 0x6d, 0xd1, 0xb6, 0x68, 0x5b, 0xb4, 0x2d, 0xda, 0x16,
  0x6d, 0x8b, 0xb6, 0x45, 0xdb, 0xa2, 0x6d, 0xd1, 0xb6, 0x68, 0x5b, 0xb4, 0x2d, 0xda, 0x16,
  0x6d, 0x8b, 0xb6, 0x0d, 3, 3, 3, 3, 0x45, 0xdb, 0xa2, 0x6d, 0xdb, 0xa2, 0x6d, 0xd1,
  0xb6, 0x68, 0x5b, 0xb4]
private def wrap64 : Bytes := .ofList ([
  0x80, 1, 4, 7, 0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 1,
  64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0, 0, 0, 0, 0, 0, 0, 0, 1] ++ List.replicate 231 0)
private def wide64 : Bytes := .ofList [0x80, 2, 2, 4, 0x80, 0xc8, 0xaf, 0xa0, 0x25, 5, 0, 0]

private def hex (bytes : Bytes) : String :=
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (physical name : String) (size minis count : Nat) (bytes : Bytes) : String :=
  String.intercalate "\t" [physical, name, toString size, toString minis, toString count, hex bytes] ++ "\n"

#guard
    (include_str "../../../../tests/formats/parquet-delta-binary-packed/parquet-java-1.16.0.tsv") =
      fixtureLine "INT32" "empty" 128 4 0 empty32 ++
      fixtureLine "INT32" "singleton" 128 4 1 singleton32 ++
      fixtureLine "INT32" "wrap" 128 4 7 wrap32 ++
      fixtureLine "INT32" "blocks" 128 4 140 blocks32 ++
      fixtureLine "INT64" "wrap" 128 4 7 wrap64 ++
      fixtureLine "INT64" "wide-miniblock" 256 2 4 wide64

private def decode32 (count : Nat) (source : Bytes) : Except Error (List Int32) :=
  decode .int32 limits count source
private def decode64 (count : Nat) (source : Bytes) : Except Error (List Int64) :=
  decode .int64 limits count source

#guard decode32 0 empty32 = .ok []
#guard decode32 1 singleton32 = .ok [-2147483648]
#guard decode32 7 wrap32 = .ok [0, -2147483648, -1, 2147483647, 0, -2147483648, 0]
#guard decode32 140 blocks32 = .ok ((List.range 140).map fun i => Int32.ofNat (1000 - 3 * i + i % 5))
#guard decode64 7 wrap64 =
  .ok [0, -9223372036854775808, -1, 9223372036854775807, 0, -9223372036854775808, 0]
#guard decode64 4 wide64 = .ok [5000000000, 4999999997, 4999999994, 4999999991]

-- First value 7, minimum −2, then one residual of 1. The padding bits are all set.
-- The three unused width octets are arbitrary and have no corresponding payloads.
private def padded : Bytes := .ofList [0x80, 1, 4, 2, 14, 3, 1, 255, 254, 253, 255, 255, 255, 255]
#guard decode32 2 padded = .ok [7, 6]
#guard (parse .int32 limits 2 padded).map (fun stream => stream.blocks.map Block.unusedWidths) =
  .ok [[255, 254, 253]]
#guard decode32 2 (.ofList (padded.toList.take 13)) = .error (.wire .truncated)
#guard decode32 2 (padded.push 0) = .error .trailingBytes
#guard decode32 0 (empty32.push 0) = .error .trailingBytes
#guard decode32 1 (singleton32.push 0) = .error .trailingBytes
#guard decode32 0 .empty = .error (.wire .truncated)
#guard decode32 1 empty32 = .error .countMismatch
#guard decode32 0 (.ofList [0x80, 0x81, 0, 4, 0, 0]) = .error (.wire .noncanonicalHeader)
#guard decode32 0 (.ofList [0x80, 1, 4, 0x80, 0x80, 0x80, 0x80, 8, 0]) = .error (.wire .headerOverflow)
#guard decode32 0 (.ofList [0x80, 1, 4, 0, 0x80, 0x80, 0x80, 0x80, 16]) = .error (.wire .headerOverflow)
#guard decode32 0 (.ofList [64, 2, 0, 0]) = .error .invalidGeometry
#guard decode32 0 (.ofList [0x80, 1, 0, 0, 0]) = .error .invalidGeometry
#guard decode32 0 (.ofList [0x80, 1, 3, 0, 0]) = .error .invalidGeometry
#guard decode32 0 (.ofList [0x80, 1, 8, 0, 0]) = .error .invalidGeometry
#guard decode32 2 (.ofList [0x80, 1, 4, 2, 0, 0, 0, 0, 0]) = .error (.wire .truncated)
#guard decode32 2 (.ofList [0x80, 1, 4, 2, 0, 0, 33, 0, 0, 0]) = .error .invalidWidth
#guard decode64 2 (.ofList [0x80, 1, 4, 2, 0, 0, 65, 0, 0, 0]) = .error .invalidWidth
#guard parse .int32 { limits with bytes := 4 } 0 empty32 = .error .byteLimit
#guard parse .int32 { limits with values := 0 } 1 singleton32 = .error .valueLimit
#guard parse .int32 { limits with blockValues := 127 } 0 empty32 = .error .geometryLimit
#guard parse .int32 { limits with miniblocksPerBlock := 3 } 0 empty32 = .error .geometryLimit
#guard parse .int32 { limits with blocks := 1 } 140 blocks32 = .error .blockLimit

end Silmaril.Formats.Parquet.DeltaBinaryPacked
