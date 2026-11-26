module

import Silmaril.Semantics.SQLite.Relational.Value.Thms

namespace Silmaril.SQLite.Relational

example : (SqlValue.ofRealBits 0x7ff8000000000001) = .null := by decide
example : (SqlValue.ofRealBits 0xfff0000000000000).storageClass = .real := by decide
example : SqlValue.ofRealBits 0 ≠ SqlValue.ofRealBits 0x8000000000000000 := by decide

example : SqlValue.text (.utf8 "a") ≠ .blob "a".toUTF8 := by decide
example : SqlValue.text (.utf8 "a") ≠ .text ⟨.utf16le, "a".toUTF8⟩ := by decide
example : (Text.utf8 "a\x00b").bytes = ⟨#[97, 0, 98]⟩ := by decide

private def tagA : PointerTag := ⟨"A".toUTF8, by decide⟩
private def tagB : PointerTag := ⟨"B".toUTF8, by decide⟩
private def pointer : ValueObject Nat .protectedValue := ⟨.pointer tagA 7⟩
private def taggedNull : ValueObject Empty .protectedValue := ⟨.sql .null (some 112)⟩

example : pointer.value.toSql = .null := rfl
example : pointer.pointer? tagA = some 7 := ValueObject.pointer?_matching _ _
example : pointer.pointer? tagB = none := ValueObject.pointer?_different (by decide) _
example : taggedNull.subtypeCode = pointer.subtypeCode := rfl
example : taggedNull.pointer? tagA = none := rfl
example : pointer.dup.value = .ofSql .null := rfl
example : taggedNull.dup.value = .ofSql .null := rfl

example : ValueObject.subtypeCode
    (ValueObject.dup (⟨.sql (.integer 7) (some 41)⟩ : ValueObject Empty .unprotectedValue)) =
      41 := rfl

end Silmaril.SQLite.Relational
