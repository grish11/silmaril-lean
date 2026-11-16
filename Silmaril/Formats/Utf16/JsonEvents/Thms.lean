module

public import Silmaril.Formats.Utf16.Thms
public import Silmaril.Formats.JsonEvents.Scalar.Defs
import Silmaril.Proofs.Formats.Utf16.JsonEvents

/-!
# UTF-16 well-formedness in JSON event payloads

`Silmaril.Formats.JsonEvents.Scalar` checks strings of the `scalarEscapes` profile with its own
`JsonEvents.Utf16.wellFormed`. It is the same predicate as `Utf16.WellFormedUnits`
(`jsonEvents_wellFormed_iff`), so a string payload valid under `scalarEscapes` is exactly the
UTF-16 encoding of a string of Unicode scalar values (`stringValid_scalarEscapes_iff`).
-/

@[expose] public section

namespace Silmaril.Formats.Utf16

/-- The JSON-event check computes the same function as `wellFormedUnitsB`. -/
theorem jsonEvents_wellFormed_eq (us : List UInt16) :
    JsonEvents.Utf16.wellFormed us = wellFormedUnitsB us :=
  Silmaril.Proofs.Formats.Utf16.JsonEvents.wellFormed_eq us

theorem jsonEvents_wellFormed_iff {us : List UInt16} :
    JsonEvents.Utf16.WellFormed us ↔ WellFormedUnits us := by
  rw [JsonEvents.Utf16.WellFormed, jsonEvents_wellFormed_eq, wellFormedUnitsB_iff]

/-- Under `scalarEscapes`, a valid string payload is the encoding of a scalar-value string. -/
theorem stringValid_scalarEscapes_iff {us : List UInt16} :
    JsonEvents.stringValid .scalarEscapes us = true ↔ ∃ cs, us = encodeUnits cs :=
  (jsonEvents_wellFormed_iff (us := us)).trans wellFormedUnits_iff_exists_chars

end Silmaril.Formats.Utf16

end
