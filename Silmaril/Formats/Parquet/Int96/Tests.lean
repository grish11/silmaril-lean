module

import Silmaril.Formats.Parquet.Int96.Defs
meta import Silmaril.Formats.Parquet.Int96.Defs
meta import Silmaril.Numeric.Gregorian.Defs
meta import Silmaril.Numeric.Timestamp.Defs
meta import Silmaril.Prelude.Bytes.Digits.Defs

open Silmaril.Formats.Parquet.Int96
open Silmaril.Numeric.Timestamp

private def epoch : Payload := ⟨2440588, ⟨0, by decide⟩⟩
private def beforeEpoch : Payload := ⟨2440587, ⟨86399999999999, by decide⟩⟩

-- Nanoseconds precede the Julian day, with each word little-endian.
#guard epoch.encode = [0, 0, 0, 0, 0, 0, 0, 0, 0x8c, 0x3d, 0x25, 0]
#guard Payload.decode? epoch.encode = some epoch
#guard Payload.decode? (epoch.encode.take 11) = none
#guard Payload.decode? (epoch.encode ++ [0]) = none
#guard Payload.decode? (Silmaril.KBytes.unpack 8 nanosecondsPerDay ++ epoch.encode.drop 8) = none
#guard Payload.decode? (List.replicate 8 255 ++ epoch.encode.drop 8) = none

#guard beforeEpoch.toGregorian.date = ⟨1969, 12, 31⟩
#guard Payload.ofGregorian? beforeEpoch.toGregorian = some beforeEpoch
#guard Payload.ofGregorian? ⟨⟨1500, 2, 29⟩, ⟨0, by decide⟩⟩ = none
#guard (Payload.ofGregorian? ⟨⟨1500, 3, 1⟩, ⟨0, by decide⟩⟩).map (·.julianDay) = some 2268983
#guard (beforeEpoch.toTicks .prolepticUtc).ticks = -1
#guard (beforeEpoch.toTicks .prolepticLocal).ticks = -1
#guard Payload.ofTicks? .prolepticLocal (⟨-1⟩ : Ticks .localReading .nanosecond) = some beforeEpoch
#guard (beforeEpoch.toInt64 .prolepticLocal .microsecond) matches .error .precisionLoss

private def minimum : Payload := ⟨Int32.minValue, ⟨0, by decide⟩⟩
private def maximum : Payload := ⟨Int32.maxValue, ⟨86399999999999, by decide⟩⟩

#guard minimum.encode.drop 8 = [0, 0, 0, 0x80]
#guard maximum.encode.drop 8 = [0xff, 0xff, 0xff, 0x7f]
#guard Payload.decode? minimum.encode = some minimum
#guard Payload.decode? maximum.encode = some maximum
#guard Payload.ofTicks? .prolepticUtc (minimum.toTicks .prolepticUtc) = some minimum
#guard Payload.ofTicks? .prolepticUtc (maximum.toTicks .prolepticUtc) = some maximum
#guard Payload.ofTicks? .prolepticLocal
    (⟨(minimum.toTicks .prolepticLocal).ticks - 1⟩ : Ticks .localReading .nanosecond) = none
#guard Payload.ofTicks? .prolepticLocal
    (⟨(maximum.toTicks .prolepticLocal).ticks + 1⟩ : Ticks .localReading .nanosecond) = none
#guard (minimum.toInt64 .prolepticUtc .nanosecond) matches .error .outOfRange
#guard (maximum.toInt64 .prolepticUtc .nanosecond) matches .error .outOfRange
