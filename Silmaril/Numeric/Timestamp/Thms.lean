module

public import Silmaril.Numeric.Timestamp.Defs
import Silmaril.Proofs.Numeric.Timestamp.Conversion

public section

namespace Silmaril.Numeric.Timestamp.Ticks

variable {kind : Kind} {source target : TickUnit}

/-- An exact conversion succeeds precisely for a result with the same denotation. -/
theorem rescale_eq_some_iff {value : Ticks kind source} {result : Ticks kind target} :
    value.rescale target = some result ↔ value.denote = result.denote :=
  Proofs.Numeric.Timestamp.rescale_eq_some_iff

/-- An exact unit conversion can always be reversed on unbounded ticks. -/
theorem rescale_roundtrip {value : Ticks kind source} {result : Ticks kind target}
    (h : value.rescale target = some result) : result.rescale source = some value :=
  rescale_eq_some_iff.mpr (rescale_eq_some_iff.mp h).symm

/-- A successful signed 64-bit conversion preserves denotation, and every payload
    whose interpretation has that denotation is returned by the conversion. -/
theorem toInt64_eq_ok_iff {value : Ticks kind source} {payload : Int64} :
    value.toInt64 target = .ok payload ↔ value.denote = (ofInt64 kind target payload).denote :=
  Proofs.Numeric.Timestamp.toInt64_eq_ok_iff

/-- Each signed 64-bit payload survives interpretation and same-unit conversion. -/
@[simp] theorem toInt64_ofInt64 (kind : Kind) (unit : TickUnit) (payload : Int64) :
    (ofInt64 kind unit payload).toInt64 unit = .ok payload :=
  toInt64_eq_ok_iff.mpr rfl

/-- A successful conversion of a signed 64-bit payload can be reversed in its original unit. -/
theorem toInt64_roundtrip {input output : Int64}
    (h : (ofInt64 kind source input).toInt64 target = .ok output) :
    (ofInt64 kind target output).toInt64 source = .ok input :=
  toInt64_eq_ok_iff.mpr (toInt64_eq_ok_iff.mp h).symm

end Silmaril.Numeric.Timestamp.Ticks
