module

import Silmaril.Formats.Parquet.Plain.Thms
meta import Silmaril.Formats.Bytes

/-! Parquet-java PLAIN payloads and malformed-input fixtures. -/

namespace Silmaril.Formats.Parquet.Plain

set_option maxRecDepth 4096

private def ints32 : List Int32 := [-2147483648, -2, 0, 0x01020304, 2147483647]
private def wire32 : Bytes := .ofList [
  0, 0, 0, 0x80, 0xfe, 0xff, 0xff, 0xff, 0, 0, 0, 0, 4, 3, 2, 1, 0xff, 0xff, 0xff, 0x7f
]

private def ints64 : List Int64 :=
  [-9223372036854775808, -2, 0, 0x0102030405060708, 9223372036854775807]
private def wire64 : Bytes := .ofList [
  0, 0, 0, 0, 0, 0, 0, 0x80,
  0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0, 0, 0, 0, 0, 0, 0, 0,
  8, 7, 6, 5, 4, 3, 2, 1,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f
]

private def booleans : List Bool :=
  [true, false, true, true, false, false, false, true, false, true, true]
private def wireBoolean : Bytes := .ofList [0x8d, 0x06]

private def fixed : List Bytes := [.ofList [0, 0xff, 0x41], .ofList [0x80, 0, 0x7f]]
private def wireFixed : Bytes := .ofList [0, 0xff, 0x41, 0x80, 0, 0x7f]

private def floats : List UInt32 := [0x80000000, 0x3fc00000, 0x7f800000]
private def wireFloat : Bytes := .ofList [0, 0, 0, 0x80, 0, 0, 0xc0, 0x3f, 0, 0, 0x80, 0x7f]

private def doubles : List UInt64 := [0x8000000000000000, 0x3ff8000000000000, 0xfff0000000000000]
private def wireDouble : Bytes := .ofList [
  0, 0, 0, 0, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0xf8, 0x3f, 0, 0, 0, 0, 0, 0, 0xf0, 0xff
]

private def fixtureLine (name : String) (count : Nat) (payload : Bytes) : String :=
  let hex := String.ofList (payload.toList.flatMap fun byte =>
    [(byte.toNat / 16).digitChar, (byte.toNat % 16).digitChar])
  name ++ "\t" ++ toString count ++ "\t" ++ hex ++ "\n"

-- Bind the octets used below to the independently reproduced payload manifest.
#guard
    (include_str "../../../../tests/formats/parquet-plain/parquet-java-1.16.0.tsv") =
      fixtureLine "INT32" ints32.length wire32 ++
      fixtureLine "INT64" ints64.length wire64 ++
      fixtureLine "BOOLEAN" booleans.length wireBoolean ++
      fixtureLine "FIXED_LEN_BYTE_ARRAY(3)" fixed.length wireFixed ++
      fixtureLine "FLOAT" floats.length wireFloat ++
      fixtureLine "DOUBLE" doubles.length wireDouble

example : decodeInt32 5 wire32 = .ok ints32 := rfl
example : encodeInt32 ints32 = wire32 := rfl
example : decodeInt64 5 wire64 = .ok ints64 := rfl
example : encodeInt64 ints64 = wire64 := rfl
example : encodeInt32Checked [-2147483648, -2, 0, 0x01020304, 2147483647] = .ok wire32 := rfl
example : encodeInt64Checked
    [-9223372036854775808, -2, 0, 0x0102030405060708, 9223372036854775807] = .ok wire64 := rfl
example : encodeInt32Checked [-2147483649] = .error .integerOverflow := rfl
example : encodeInt32Checked [0, 2147483648] = .error .integerOverflow := rfl
example : encodeInt64Checked [-9223372036854775809] = .error .integerOverflow := rfl
example : encodeInt64Checked [9223372036854775808] = .error .integerOverflow := rfl
example : decodeInt32 1 (.ofList [1, 2, 3]) = .error .truncated := rfl
example : decodeInt32 1 (.ofList [1, 2, 3, 4, 5]) = .error .trailingBytes := rfl
example : decodeInt32 4 wire32 = .error .trailingBytes := rfl
example : decodeInt64 6 wire64 = .error .truncated := rfl
example : decodeInt64 (2 ^ 64) .empty = .error .truncated := rfl
example : decodeInt32 0 .empty = .ok [] := rfl
example : decodeInt64 0 (.ofList [0]) = .error .trailingBytes := rfl

example : decodeBoolean 11 wireBoolean = .ok booleans := rfl
example : encodeBoolean booleans = wireBoolean := rfl
example : decodeBoolean 11 (.ofList [0x8d, 0xfe]) = .ok booleans := rfl
example : decodeBoolean 8 wireBoolean = .error .trailingBytes := rfl
example : decodeBoolean 9 (.ofList [0x8d]) = .error .truncated := rfl
example : decodeBoolean (2 ^ 64) .empty = .error .truncated := rfl
example : decodeBoolean 0 (.ofList [0]) = .error .trailingBytes := rfl
example : decodeBoolean 0 .empty = .ok [] := rfl
example : encodeBoolean [] = .empty := rfl
example : encodeBoolean [true, false, true, false, true, false, true, false] = .ofList [0x55] := rfl

example : decodeFixedLenBytes 3 2 wireFixed = .ok fixed := rfl
example : encodeFixedLenBytes 3 fixed = .ok wireFixed := rfl
example : decodeFixedLenBytes 0 0 .empty = .error .invalidWidth := rfl
example : decodeFixedLenBytes (2 ^ 31) 0 .empty = .error .invalidWidth := rfl
example : encodeFixedLenBytes 2 fixed = .error .elementWidthMismatch := rfl
example : decodeFixedLenBytes 3 2 (.ofList [1, 2, 3, 4, 5]) = .error .truncated := rfl
example : decodeFixedLenBytes 3 1 wireFixed = .error .trailingBytes := rfl

example : decodeFloatBits 3 wireFloat = .ok floats := rfl
example : encodeFloatBits floats = wireFloat := rfl
example : decodeDoubleBits 3 wireDouble = .ok doubles := rfl
example : encodeDoubleBits doubles = wireDouble := rfl

-- Hand-derived noncanonical NaN payloads. These use the raw bits API.
example : decodeFloatBits 1 (.ofList [0x34, 0x12, 0xc0, 0x7f]) = .ok [0x7fc01234] := rfl
example : encodeFloatBits [0x7fc01234] = .ofList [0x34, 0x12, 0xc0, 0x7f] := rfl
example : decodeDoubleBits 1 (.ofList [1, 0, 0, 0, 0, 0, 0xf8, 0x7f]) =
    .ok [0x7ff8000000000001] := rfl
example : encodeDoubleBits [0x7ff8000000000001] =
    .ofList [1, 0, 0, 0, 0, 0, 0xf8, 0x7f] := rfl

end Silmaril.Formats.Parquet.Plain
