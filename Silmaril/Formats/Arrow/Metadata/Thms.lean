module

public import Silmaril.Formats.Arrow.Metadata.Defs

/-! Normalization of reader-only Arrow Schema type payloads. -/

public section

namespace Silmaril.Formats.Arrow.SchemaReader.DateUnit

/-- Accept exactly the pinned IDL units after applying the MILLISECOND default. -/
theorem normalize_eq_ok_iff (encoded : Option Nat) (unit : DateUnit) :
    normalize encoded = .ok unit ↔ encoded.getD 1 = unit.code := by
  unfold normalize
  split <;> cases unit <;> simp_all [code]

/-- Codes outside DAY and MILLISECOND are malformed. -/
theorem normalize_eq_error_iff (encoded : Option Nat) :
    normalize encoded = .error (.malformed .flatbuffer) ↔
      encoded.getD 1 ≠ 0 ∧ encoded.getD 1 ≠ 1 := by
  unfold normalize
  split <;> simp_all

end Silmaril.Formats.Arrow.SchemaReader.DateUnit

namespace Silmaril.Formats.Arrow.SchemaReader.TimestampUnit

/-- Accept exactly the pinned IDL units after applying the SECOND default. -/
theorem normalize_eq_ok_iff (encoded : Option Nat) (unit : TimestampUnit) :
    normalize encoded = .ok unit ↔ encoded.getD 0 = unit.code := by
  unfold normalize
  split <;> cases unit <;> simp_all [code]

/-- Values above the last Timestamp unit code are malformed. -/
theorem normalize_eq_error_iff (encoded : Option Nat) :
    normalize encoded = .error (.malformed .flatbuffer) ↔ 3 < encoded.getD 0 := by
  unfold normalize
  split <;> simp_all <;> omega

end Silmaril.Formats.Arrow.SchemaReader.TimestampUnit
