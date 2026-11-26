module

import Silmaril.Formats.ThriftCompact.Thms

/-! Known wire bytes and rejection checks, evaluated by Lean. -/

namespace Silmaril.Formats.ThriftCompact
set_option maxRecDepth 4096

-- Apache's unsigned example: 95 + 9 * 128 + 3 * 16384 = 50399.
example : readVarint .i32 .canonical (.ofList [0xdf, 0x89, 0x03, 0xa5]) 0 =
    .ok (50399, 3) := rfl

-- ZigZag(-65) = 129 = 1 + 1 * 128. ZigZag(64) = 128 = 0 + 1 * 128.
example : encodeSigned? .i32 (-65) = some (.ofList [0x81, 0x01]) := by decide +kernel
example : encodeSigned? .i16 64 = some (.ofList [0x80, 0x01]) := by decide +kernel
example : encodeSigned? .i16 (-32769) = none := by decide +kernel
example : encodeSigned? .i16 32768 = none := by decide +kernel

example : readSigned .i16 .canonical (.ofList [0xff, 0xff, 0x03]) 0 =
    .ok (-32768, 3) := rfl
example : readSigned .i32 .canonical (.ofList [0xfe, 0xff, 0xff, 0xff, 0x0f]) 0 =
    .ok (2147483647, 5) := rfl
example : readSigned .i64 .canonical (.ofList
    [0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 1]) 0 =
    .ok (9223372036854775807, 10) := rfl

example : readVarint .i16 .canonical (.ofList [0x81, 0x00, 0x99]) 0 =
    .error .noncanonicalVarint := rfl
example : readVarint .i16 .permissive (.ofList [0x81, 0x00, 0x99]) 0 =
    .ok (1, 2) := rfl
example : readVarint .i16 .canonical (.ofList [0x80]) 0 =
    .error .truncated := rfl
example : readVarint .i16 .permissive (.ofList [0x80, 0x80, 0x80, 0x00]) 0 =
    .error .varintOverflow := rfl
example : readVarint .i16 .canonical (.ofList [0x80, 0x80, 0x04]) 0 =
    .error .varintOverflow := rfl
example : readVarint .i64 .permissive (.ofList
    [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02]) 0 =
    .error .varintOverflow := rfl

example : readI8 (.ofList [0x80]) 0 = .ok (-128, 1) := rfl
example : readBool (.ofList [2, 1]) 0 = .ok (false, 1) := rfl
example : readBool (.ofList [2, 1]) 1 = .ok (true, 2) := rfl
example : readBool (.ofList [0]) 0 = .error .invalidBoolean := rfl

-- Little-endian raw bits for IEEE 754 negative zero and a NaN payload.
example : readDoubleBits (.ofList [0, 0, 0, 0, 0, 0, 0, 0x80, 0x55]) 0 =
    .ok (0x8000000000000000, 8) := rfl
example : readDoubleBits (.ofList [1, 0, 0, 0, 0, 0, 0xf8, 0x7f]) 0 =
    .ok (0x7ff8000000000001, 8) := rfl
example : readDoubleBits (.ofList [0, 0, 0, 0, 0, 0, 0]) 0 =
    .error .truncated := rfl
example : readUuid (.ofList [0xa5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]) 1 =
    .ok (.ofList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], 17) := rfl

example : readBinary .canonical 0 (.ofList [0, 0xa5]) 0 = .ok (.empty, 1) := rfl
example : readBinary .canonical 4 (.ofList [3, 0x61, 0x62]) 0 =
    .error .truncated := rfl
example : readBinary .canonical 2 (.ofList [3, 0x61, 0x62, 0x63]) 0 =
    .error .lengthLimit := rfl
example : readLength .canonical 2147483647 (.ofList [0xff, 0xff, 0xff, 0xff, 7]) 0 =
    .ok (2147483647, 5) := rfl
example : readLength .canonical 2147483648 (.ofList [0x80, 0x80, 0x80, 0x80, 8]) 0 =
    .error .lengthOverflow := rfl
example : readString .canonical 4 (.ofList [3, 0xc3, 0xa9, 0x00, 0xa5]) 0 =
    .ok ("é\x00", 4) := rfl
example : readString .canonical 4 (.ofList [2, 0xc0, 0x80]) 0 =
    .error .invalidUtf8 := rfl

-- From the wire rules, checked independently against Apache Thrift v0.23.0's
-- Python writer (see the guide). 0xa5 after STOP represents unread input.
private def structFixture : Bytes := .ofList [
  0x15, 0x81, 0x01,                 -- i32 field 1, -65
  0x11, 0xf2,                       -- true at 2, false at 17
  0x08, 0x42, 0x03, 0x00, 0xff, 0x41,  -- binary field 33 (delta 16), three octets
  0x06, 0x03,                       -- i64 field -2, explicit signed field ID
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01, -- minimum i64
  0x59, 0x24, 0x80, 0x01, 0xff, 0x01,  -- list<i16> field 3, [64, -128]
  0x00, 0xa5
]

example : readFieldHeader .canonical 0 structFixture 0 =
    .ok (.field 1 (.payload .i32), 1) := rfl
example : readSigned .i32 .canonical structFixture 1 = .ok (-65, 3) := rfl
example : readFieldHeader .canonical 1 structFixture 3 =
    .ok (.field 2 (.bool true), 4) := rfl
example : readFieldHeader .canonical 2 structFixture 4 =
    .ok (.field 17 (.bool false), 5) := rfl
example : readFieldHeader .canonical 17 structFixture 5 =
    .ok (.field 33 (.payload .binary), 7) := rfl
example : readBinary .canonical 3 structFixture 7 =
    .ok (.ofList [0x00, 0xff, 0x41], 11) := rfl
example : readFieldHeader .canonical 33 structFixture 11 =
    .ok (.field (-2) (.payload .i64), 13) := rfl
example : readSigned .i64 .canonical structFixture 13 =
    .ok (-9223372036854775808, 23) := rfl
example : readFieldHeader .canonical (-2) structFixture 23 =
    .ok (.field 3 (.payload .list), 24) := rfl
example : readCollectionHeader .canonical 2 structFixture 24 = .ok (⟨2, .i16⟩, 25) := rfl
example : readSigned .i16 .canonical structFixture 25 = .ok (64, 27) := rfl
example : readSigned .i16 .canonical structFixture 27 = .ok (-128, 29) := rfl
example : readFieldHeader .canonical 3 structFixture 29 = .ok (.stop, 30) := rfl

example : readFieldHeader .canonical 32767 (.ofList [0x15]) 0 =
    .error .fieldIdOverflow := rfl
example : readFieldHeader .canonical 0 (.ofList [0x10, 0x15]) 0 =
    .error (.invalidType 0) := rfl
example : readFieldHeader .canonical 0 (.ofList [0x0e]) 0 =
    .error (.invalidType 14) := rfl
example : readFieldHeader .canonical 0 (.ofList [0x05, 0x80]) 0 =
    .error .truncated := rfl

example : readCollectionHeader .canonical 14 (.ofList [0xe1]) 0 = .ok (⟨14, .bool⟩, 1) := rfl
example : readCollectionHeader .canonical 15 (.ofList [0xf2, 15, 1]) 0 =
    .ok (⟨15, .bool⟩, 2) := rfl
example : readCollectionHeader .permissive 15 (.ofList [0xf2, 14]) 0 =
    .error .invalidCollectionSize := rfl
example : readCollectionHeader .canonical 14 (.ofList [0xf1, 15]) 0 =
    .error .lengthLimit := rfl
example : readMapHeader .canonical 0 (.ofList [0, 0x85]) 0 = .ok (.empty, 1) := rfl
example : readMapHeader .canonical 1 (.ofList [1, 0x85]) 0 =
    .ok (.entries 1 .binary .i32, 2) := rfl
example : readMapHeader .canonical 1 (.ofList [1]) 0 = .error .truncated := rfl

end Silmaril.Formats.ThriftCompact
