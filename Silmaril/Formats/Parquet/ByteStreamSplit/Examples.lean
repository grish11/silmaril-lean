module

import Silmaril.Formats.Parquet.ByteStreamSplit.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.ByteStreamSplit.Defs
meta import Batteries.Data.Except

/-! Independent producer bytes and exact lane and rejection cases. -/

namespace Silmaril.Formats.Parquet.ByteStreamSplit

private def limits : Limits := ⟨4, 32, 8⟩
private def int32Lanes : Bytes := .ofList [
  0, 0xfe, 4, 0xff, 0, 0xff, 3, 0xff, 0, 0xff, 2, 0xff, 0x80, 0xff, 1, 0x7f]
private def int64Lanes : Bytes := .ofList [
  0, 0xfe, 8, 0xff, 0, 0xff, 7, 0xff, 0, 0xff, 6, 0xff, 0, 0xff, 5, 0xff,
  0, 0xff, 4, 0xff, 0, 0xff, 3, 0xff, 0, 0xff, 2, 0xff, 0x80, 0xff, 1, 0x7f]
private def floatLanes : Bytes := .ofList (List.replicate 8 0 ++
  [0, 0xa0, 0x80, 0xc0, 0x80, 0x3f, 0xff, 0x7f])
private def doubleLanes : Bytes := .ofList (List.replicate 24 0 ++
  [0, 0xf4, 0xf0, 0xf8, 0x80, 0x3f, 0xff, 0x7f])
private def fixedLanes : Bytes := .ofList [0, 0x80, 0x11, 0xff, 0, 0x22, 0x41, 0x7f, 0x33]
private def floatPayloads : Bytes := .ofList [0x45, 0x21, 1, 0x23, 0x43, 0, 0xc1, 0xc5, 0, 0x7f, 0xff, 0]
private def doublePayloads : Bytes := .ofList [
  0xbc, 0x45, 1, 0x9a, 0x23, 0, 0x78, 1, 0, 0x56, 0xef, 0,
  0x34, 0xcd, 0, 0x12, 0xab, 0, 0xf8, 0xf8, 0, 0x7f, 0xff, 0]

private def hex (bytes : Bytes) : String :=
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (name : String) (count width : Nat) (body : Bytes) : String :=
  String.intercalate "\t" [name, toString count, toString width, hex body] ++ "\n"

#guard (include_str "../../../../tests/formats/parquet-byte-stream-split/pyarrow-26.0.1.tsv") =
  fixtureLine "INT32" 4 4 int32Lanes ++ fixtureLine "INT64" 4 8 int64Lanes ++
  fixtureLine "FLOAT" 4 4 floatLanes ++ fixtureLine "DOUBLE" 4 8 doubleLanes ++
  fixtureLine "FIXED_LEN_BYTE_ARRAY" 3 3 fixedLanes ++ fixtureLine "FLOAT_NAN_PAYLOAD" 3 4 floatPayloads ++
  fixtureLine "DOUBLE_NAN_PAYLOAD" 3 8 doublePayloads

#guard decode .int32 limits 4 int32Lanes = .ok [-2147483648, -2, 0x01020304, 2147483647]
#guard decode .int64 limits 4 int64Lanes =
  .ok [-9223372036854775808, -2, 0x0102030405060708, 9223372036854775807]
#guard decode .floatBits limits 4 floatLanes = .ok [0x80000000, 0x3fa00000, 0xff800000, 0x7fc00000]
#guard decode .doubleBits limits 4 doubleLanes =
  .ok [0x8000000000000000, 0x3ff4000000000000, 0xfff0000000000000, 0x7ff8000000000000]
#guard decode (.fixedLenBytes 3) limits 3 fixedLanes =
  .ok [.ofList [0, 0xff, 0x41], .ofList [0x80, 0, 0x7f], .ofList [0x11, 0x22, 0x33]]
#guard decode .floatBits limits 3 floatPayloads = .ok [0x7fc12345, 0xffc54321, 1]
#guard decode .doubleBits limits 3 doublePayloads = .ok [0x7ff8123456789abc, 0xfff8abcdef012345, 1]

-- The specification's asymmetric example distinguishes lane-major from word-major order.
#guard decodeWords limits 4 3 (.ofList [0xaa, 0, 0xa3, 0xbb, 0x11, 0xb4, 0xcc, 0x22, 0xc5, 0xdd, 0x33, 0xd6]) =
  .ok [[0xaa, 0xbb, 0xcc, 0xdd], [0, 0x11, 0x22, 0x33], [0xa3, 0xb4, 0xc5, 0xd6]]
#guard decodeWords limits 1 3 (.ofList [0, 0xff, 0x80]) = .ok [[0], [0xff], [0x80]]
#guard decodeWords limits 3 1 (.ofList [0, 0xff, 0x80]) = .ok [[0, 0xff, 0x80]]
#guard decode .int64 limits 0 .empty = .ok []
#guard decode .floatBits limits 0 (.ofList [0]) = .error .trailingBytes
#guard decode (.fixedLenBytes 0) limits 0 .empty = .error .invalidWidth
#guard decode (.fixedLenBytes (2 ^ 31)) limits 0 .empty = .error .invalidWidth
#guard decode (.fixedLenBytes 9) limits 0 .empty = .error .widthLimit
#guard decodeWords { limits with values := 2 ^ 31 } 4 (2 ^ 31) .empty = .error .valueLimit
#guard decodeWords { limits with values := 3 } 4 4 int32Lanes = .error .valueLimit
#guard decodeWords { limits with bytes := 15 } 4 4 int32Lanes = .error .byteLimit
#guard decodeWords limits 4 4 (.ofList (int32Lanes.toList.take 15)) = .error .truncated
#guard decodeWords limits 4 4 (int32Lanes.push 0) = .error .trailingBytes
#guard decodeWords limits 4 3 int32Lanes = .error .trailingBytes
#guard decodeWords limits 2 3 fixedLanes = .error .trailingBytes
#guard decodeWords { limits with width := 2 ^ 30 } (2 ^ 30) 4 .empty = .error .truncated

end Silmaril.Formats.Parquet.ByteStreamSplit
