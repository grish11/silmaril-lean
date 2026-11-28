module

public import Silmaril.Numeric.UnixRepresentation.Defs
import Silmaril.Proofs.Numeric.UnixRepresentation.Integer
import Silmaril.Proofs.Numeric.UnixRepresentation.Civil

public section

namespace Silmaril.Numeric.UnixRepresentation

open Timestamp

variable {kind : Kind} {source target : TickUnit}

/-- Floor discards a nonnegative offset strictly smaller than one destination tick. -/
theorem quantize_floor {value : Ticks kind source} {rounded : Ticks kind target}
    (h : quantize value target .floor = some rounded) :
    0 ≤ value.denote.ticks - rounded.denote.ticks ∧
      value.denote.ticks - rounded.denote.ticks < target.nanosecondsPerTick :=
  Proofs.Numeric.UnixRepresentation.quantize_floor h

/-- Truncation discards less than one destination tick, toward zero on either side. -/
theorem quantize_trunc {value : Ticks kind source} {rounded : Ticks kind target}
    (h : quantize value target .trunc = some rounded) :
    let error := value.denote.ticks - rounded.denote.ticks;
    -target.nanosecondsPerTick < error ∧ error < target.nanosecondsPerTick ∧
      (0 ≤ value.denote.ticks → 0 ≤ error) ∧ (value.denote.ticks ≤ 0 → error ≤ 0) :=
  Proofs.Numeric.UnixRepresentation.quantize_trunc h

namespace WordFormat

variable {format : WordFormat}

theorem toInt_inRange (payload : format.Payload) : format.InRange (format.toInt payload) :=
  Proofs.Numeric.UnixRepresentation.WordFormat.toInt_inRange payload

@[simp] theorem toInt_ofInt {count : Int} (h : format.InRange count) :
    format.toInt (format.ofInt count h) = count :=
  Proofs.Numeric.UnixRepresentation.WordFormat.toInt_ofInt h

/-- The successful payload decodes to the chosen destination count. -/
theorem encode_eq_ok_iff {value : Ticks kind source} {rounding : TickRounding}
    {payload : format.Payload} :
    format.encode value target rounding = .ok payload ↔
      quantize value target rounding = some (format.decode kind target payload) :=
  Proofs.Numeric.UnixRepresentation.WordFormat.encode_eq_ok_iff

/-- A payload exists exactly when quantization succeeds and its count is in range. -/
theorem encode_exists_iff {value : Ticks kind source} {rounding : TickRounding} :
    (∃ payload, format.encode value target rounding = .ok payload) ↔
      ∃ count : Ticks kind target, quantize value target rounding = some count ∧
        format.InRange count.ticks :=
  Proofs.Numeric.UnixRepresentation.WordFormat.encode_exists_iff

/-- Exact conversion returns precisely the payload with the same offset. -/
theorem encode_exact_eq_ok_iff {value : Ticks kind source} {payload : format.Payload} :
    format.encode value target .exact = .ok payload ↔
      value.denote = (format.decode kind target payload).denote :=
  Proofs.Numeric.UnixRepresentation.WordFormat.encode_exact_eq_ok_iff

/-- A remainder in the destination unit takes precedence over any range check. -/
theorem encode_exact_eq_precisionLoss_iff {value : Ticks kind source} :
    format.encode value target .exact = .error .precisionLoss ↔
      value.denote.ticks % target.nanosecondsPerTick ≠ 0 :=
  Proofs.Numeric.UnixRepresentation.WordFormat.encode_exact_eq_precisionLoss_iff

/-- Range failure refers to the already quantized count. -/
theorem encode_eq_outOfRange_iff {value : Ticks kind source} {rounding : TickRounding} :
    format.encode value target rounding = .error .outOfRange ↔
      ∃ count : Ticks kind target, quantize value target rounding = some count ∧
        ¬ format.InRange count.ticks :=
  Proofs.Numeric.UnixRepresentation.WordFormat.encode_eq_outOfRange_iff

@[simp] theorem encode_decode (format : WordFormat) (kind : Kind) (unit : TickUnit)
    (payload : format.Payload) :
    format.encode (format.decode kind unit payload) unit .exact = .ok payload :=
  encode_exact_eq_ok_iff.mpr rfl

/-- A successful exact conversion reverses, including across widths and units. -/
theorem encode_exact_roundtrip {other : WordFormat} {input : format.Payload}
    {output : other.Payload}
    (h : other.encode (format.decode kind source input) target .exact = .ok output) :
    format.encode (other.decode kind target output) source .exact = .ok input :=
  encode_exact_eq_ok_iff.mpr (encode_exact_eq_ok_iff.mp h).symm

/-- The exact signed 64-bit API agrees with the existing Timestamp conversion. -/
theorem encode_int64_exact (value : Ticks kind source) (target : TickUnit) :
    WordFormat.int64.encode value target .exact = value.toInt64 target := rfl

end WordFormat

namespace Timespec

@[simp] theorem toTicks_ofTicks {unit : TickUnit} (value : Ticks kind unit) :
    (ofTicks value).toTicks = value.denote :=
  Proofs.Numeric.UnixRepresentation.toTicks_ofTicks value

@[simp] theorem ofTicks_toTicks (value : Timespec kind) : ofTicks value.toTicks = value :=
  Proofs.Numeric.UnixRepresentation.ofTicks_toTicks value

end Timespec

namespace CivilTime

@[simp] theorem toTimespec?_ofTimespec (value : Timespec kind) :
    (ofTimespec value).toTimespec? kind = some value :=
  Proofs.Numeric.UnixRepresentation.civil_encode_decode value

theorem ofTimespec_toTimespec? {civil : CivilTime} {value : Timespec kind}
    (h : civil.toTimespec? kind = some value) : ofTimespec value = civil :=
  Proofs.Numeric.UnixRepresentation.civil_decode_encode h

@[simp] theorem toTicks?_ofTicks {unit : TickUnit} (value : Ticks kind unit) :
    (ofTicks value).toTicks? kind = some value.denote := by
  simp [toTicks?, ofTicks]

/-- A civil encoding is recovered by decoding any ticks with that denotation. -/
theorem ofTicks_toTicks? {unit : TickUnit} {civil : CivilTime} {value : Ticks kind unit}
    (h : civil.toTicks? kind = some value.denote) : ofTicks value = civil :=
  Proofs.Numeric.UnixRepresentation.civil_ofTicks_toTicks? h

end CivilTime

end Silmaril.Numeric.UnixRepresentation
