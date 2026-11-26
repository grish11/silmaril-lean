module

import Silmaril.Semantics.SQLite.Relational.Affinity.Thms
meta import Silmaril.Semantics.SQLite.Relational.Affinity.Defs

namespace Silmaril.SQLite.Relational

#guard Affinity.ofDeclaredType (some "FLoATing POINT") == .integer
#guard Affinity.ofDeclaredType (some "CHARBLOB") == .text
#guard Affinity.ofDeclaredType (some "DOUBBLOB") == .blob
#guard Affinity.ofDeclaredType (some "DOUBLE") == .real
example : Affinity.ofDeclaredType none = .blob := rfl
#guard Affinity.ofDeclaredType (some "") == .numeric
#guard StrictType.ofDeclaredType (some "InT") == some .int
#guard StrictType.ofDeclaredType (some "VARCHAR(20)") == none

private def padded : SqlValue := .text (.utf8 "000123")

#guard (ColumnType.apply (.ordinary (Affinity.ofDeclaredType (some "ANY"))) padded).toOption ==
  some (.integer 123)
example : ColumnType.apply (.strict .any) padded = .ok padded := rfl

example : Affinity.numeric.apply (.text (.utf8 "\t+000123\r\n")) = .ok (.integer 123) := rfl
example : Affinity.numeric.apply (.text (.utf8 "-9223372036854775808")) =
    .ok (.integer Int64.minValue) := rfl
example : Affinity.numeric.apply (.text (.utf8 "9223372036854775807")) =
    .ok (.integer Int64.maxValue) := rfl
example : Affinity.numeric.apply (.text (.utf8 "9223372036854775808")) =
    .error (.unsupported .numericTextOverflow) := rfl
example : Affinity.numeric.apply (.text (.utf8 "3.0e+5")) =
    .error (.unsupported .numericTextRealSyntax) := rfl
example : Affinity.numeric.apply (.text (.utf8 "1e+")) = .ok (.text (.utf8 "1e+")) := rfl
example : Affinity.numeric.apply (.text (.utf8 "0x20")) = .ok (.text (.utf8 "0x20")) := rfl
example : Affinity.numeric.apply (.text (.utf8 "9\x009")) =
    .error (.unsupported .numericTextNul) := rfl
example : Affinity.numeric.apply (.text ⟨.utf16le, ⟨#[49, 0]⟩⟩) =
    .error (.unsupported .numericTextEncoding) := rfl

example : Affinity.numeric.apply (SqlValue.ofRealBits 0x3ff0000000000000) =
    .ok (.integer 1) := rfl
example : Affinity.numeric.apply (SqlValue.ofRealBits 0xc3e0000000000000) =
    .ok (SqlValue.ofRealBits 0xc3e0000000000000) := rfl
example : ColumnType.apply (.strict .integer) (SqlValue.ofRealBits 0x3ff8000000000000) =
    .error (.datatype .integer .real) := rfl
example : ColumnType.apply (.strict .int) (.text (.utf8 "1.5")) =
    .error (.unsupported .numericTextRealSyntax) := rfl
example : ColumnType.apply (.strict .real) (.integer 9007199254740993) =
    .ok (SqlValue.ofRealBits 0x4340000000000000) := rfl
example : ColumnType.apply (.strict .real) (.integer 9007199254740995) =
    .ok (SqlValue.ofRealBits 0x4340000000000002) := rfl
example : ColumnType.apply (.strict .real) (SqlValue.ofRealBits 0x8000000000000000) =
    .ok (SqlValue.ofRealBits 0) := rfl
#guard (ColumnType.apply (.strict .text) (.integer Int64.minValue)).toOption ==
  some (.text (.utf8 "-9223372036854775808"))
example : Affinity.text.apply (SqlValue.ofRealBits 0x3ff8000000000000) =
    .error (.unsupported .realToText) := rfl
example : ColumnType.apply (.strict .blob) (.text (.utf8 "a")) =
    .error (.datatype .blob .text) := rfl

end Silmaril.SQLite.Relational
