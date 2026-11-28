module

import Silmaril.Formats.ColumnarTimestamp.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Defs
meta import Silmaril.Numeric.Gregorian.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats.ColumnarTimestamp

private def unset : Arrow.Metadata := ⟨.second, none⟩
private def empty : Arrow.Metadata := ⟨.second, some ""⟩
private def paris : Arrow.Metadata := ⟨.second, some "Europe/Paris"⟩
private def utc : Arrow.Metadata := ⟨.second, some "UTC"⟩

#guard unset.kind matches .localReading
#guard empty.kind matches .localReading
#guard empty.timezoneAnnotation = none
#guard paris.kind matches .utcInstant
#guard paris.timezoneAnnotation = some "Europe/Paris"
#guard (paris.decode (-1)).ticks = (utc.decode (-1)).ticks
#guard !(empty.parquet .millis).isAdjustedToUTC
#guard (paris.parquet .millis).isAdjustedToUTC
#guard ((paris.parquet .millis).arrow .second).timezoneAnnotation = some "UTC"

#guard (paris.toParquet .millis (-1)).toOption = some (-1000)
#guard ((paris.parquet .millis).toArrow .second (-1000)).toOption = some (-1)
#guard ((paris.parquet .millis).toArrow .second (-1001)) matches .error .precisionLoss
#guard ((paris.parquet .nanos).toArrow .nanosecond Int64.minValue).toOption = some Int64.minValue
#guard ((paris.parquet .nanos).toArrow .nanosecond Int64.maxValue).toOption = some Int64.maxValue
#guard (paris.toParquet .nanos Int64.minValue) matches .error .outOfRange
#guard (paris.toParquet .nanos Int64.maxValue) matches .error .outOfRange

-- The local day split uses a nonnegative subday even one nanosecond before the epoch.
private def localNanos : Parquet.Metadata := ⟨.nanos, false⟩
private def beforeEpoch := LocalDateTime.ofTicks (localNanos.decode (-1))

#guard beforeEpoch.date = ⟨1969, 12, 31⟩
#guard beforeEpoch.nanosecondOfDay.val = 86399999999999
#guard beforeEpoch.toTicks?.map (·.ticks) = some (-1)
#guard (LocalDateTime.ofTicks ((⟨.millis, false⟩ : Parquet.Metadata).decode 172800000)).date =
    ⟨1970, 1, 3⟩
#guard (⟨⟨1900, 2, 29⟩, ⟨0, by decide⟩⟩ : LocalDateTime).toTicks? = none
