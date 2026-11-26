module

public import Silmaril.Formats.ColumnarTimestamp.Defs
import Silmaril.Numeric.Timestamp.Thms
import Silmaril.Proofs.Formats.ColumnarTimestamp.Contracts

/-! # Exactness and metadata laws for signed timestamp payloads -/

public section

namespace Silmaril.Formats.ColumnarTimestamp

open Silmaril.Numeric.Timestamp

variable {kind : Kind} {source target : TickUnit}

/-- A successful payload encoding is exactly an equality of nanosecond coordinates. -/
theorem toInt64_eq_ok_iff {value : Ticks kind source} {payload : Int64} :
    value.toInt64 target = .ok payload ↔
      value.denote.ticks = payload.toInt * target.nanosecondsPerTick :=
  Ticks.toInt64_eq_ok_iff.trans ⟨congrArg Ticks.ticks, congrArg Ticks.mk⟩

theorem toInt64_eq_precisionLoss_iff (value : Ticks kind source) :
    value.toInt64 target = .error .precisionLoss ↔
      value.denote.ticks % target.nanosecondsPerTick ≠ 0 :=
  Proofs.Formats.ColumnarTimestamp.toInt64_eq_precisionLoss_iff value

theorem toInt64_eq_outOfRange_iff (value : Ticks kind source) :
    let nanos := value.denote.ticks
    let scale := target.nanosecondsPerTick
    value.toInt64 target = .error .outOfRange ↔ nanos % scale = 0 ∧
      ¬ (Int64.minValue.toInt ≤ nanos / scale ∧ nanos / scale ≤ Int64.maxValue.toInt) :=
  Proofs.Formats.ColumnarTimestamp.toInt64_eq_outOfRange_iff value

namespace Arrow.Metadata

theorem kind_eq_utcInstant_iff (metadata : Arrow.Metadata) :
    metadata.kind = .utcInstant ↔ ∃ name, metadata.timezone = some name ∧ name ≠ "" :=
  Proofs.Formats.ColumnarTimestamp.arrow_kind_eq_utcInstant_iff metadata

@[simp] theorem parquet_kind (metadata : Arrow.Metadata) (unit : Parquet.TimeUnit) :
    (metadata.parquet unit).kind = metadata.kind := rfl

@[simp] theorem encode_decode (metadata : Arrow.Metadata) (payload : Int64) :
    metadata.encode (metadata.decode payload) = .ok payload :=
  Ticks.toInt64_ofInt64 _ _ _

theorem toParquet_eq_ok_iff (metadata : Arrow.Metadata) (unit : Parquet.TimeUnit)
    {input output : Int64} : metadata.toParquet unit input = .ok output ↔
      (metadata.decode input).denote.ticks = ((metadata.parquet unit).decode output).denote.ticks :=
  toInt64_eq_ok_iff

end Arrow.Metadata

namespace Parquet.Metadata

theorem kind_eq_utcInstant_iff (metadata : Parquet.Metadata) :
    metadata.kind = .utcInstant ↔ metadata.isAdjustedToUTC = true := by
  cases h : metadata.isAdjustedToUTC <;> simp [kind, epochKind, h]

@[simp] theorem arrow_kind (metadata : Parquet.Metadata) (unit : TickUnit) :
    (metadata.arrow unit).kind = metadata.kind := by
  cases h : metadata.isAdjustedToUTC <;>
    simp [arrow, Arrow.Metadata.kind, Arrow.Metadata.timezoneAnnotation, kind, epochKind, h]

@[simp] theorem encode_decode (metadata : Parquet.Metadata) (payload : Int64) :
    metadata.encode (metadata.decode payload) = .ok payload :=
  Ticks.toInt64_ofInt64 _ _ _

theorem toArrow_eq_ok_iff (metadata : Parquet.Metadata) (unit : TickUnit) {input output : Int64} :
    metadata.toArrow unit input = .ok output ↔
      (metadata.decode input).denote.ticks = ((metadata.arrow unit).decode output).denote.ticks :=
  toInt64_eq_ok_iff

theorem toArrow_roundtrip {metadata : Parquet.Metadata} {unit : TickUnit} {input output : Int64}
    (h : metadata.toArrow unit input = .ok output) :
    (metadata.arrow unit).toParquet metadata.unit output = .ok input :=
  ((metadata.arrow unit).toParquet_eq_ok_iff metadata.unit).mpr
    ((metadata.toArrow_eq_ok_iff unit).mp h).symm

end Parquet.Metadata

/-- A successful Arrow to Parquet conversion recovers the source count in its original unit.
    The original Arrow annotation must be retained separately if needed. -/
theorem Arrow.Metadata.toParquet_roundtrip {metadata : Arrow.Metadata} {unit : Parquet.TimeUnit}
    {input output : Int64} (h : metadata.toParquet unit input = .ok output) :
    (metadata.parquet unit).toArrow metadata.unit output = .ok input :=
  Ticks.toInt64_roundtrip h

namespace LocalDateTime

theorem toTicks?_ofTicks {unit : TickUnit} (value : Ticks .localReading unit) :
    (ofTicks value).toTicks? = some value.denote :=
  Proofs.Formats.ColumnarTimestamp.local_toTicks?_ofTicks value

theorem ofTicks_toTicks? {value : LocalDateTime} {ticks : Ticks .localReading .nanosecond}
    (h : value.toTicks? = some ticks) : ofTicks ticks = value :=
  Proofs.Formats.ColumnarTimestamp.local_ofTicks_toTicks? h

end LocalDateTime

end Silmaril.Formats.ColumnarTimestamp
