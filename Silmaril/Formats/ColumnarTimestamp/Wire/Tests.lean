module

import Silmaril.Formats.ColumnarTimestamp.Wire.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Wire.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Defs
meta import Silmaril.Formats.Parquet.Plain.Defs
meta import Silmaril.Numeric.Timestamp.Defs
meta import Silmaril.Formats.Bytes

namespace Silmaril.Formats.ColumnarTimestamp.Wire.Tests

open Numeric.Timestamp

private def secondsLocal : Arrow.Metadata := ⟨.second, none⟩
private def microsUtc : Parquet.Metadata := ⟨.micros, true⟩
private def nanosLocal : Parquet.Metadata := ⟨.nanos, false⟩
private def minusTwo : Bytes := Bytes.ofList [254, 255, 255, 255, 255, 255, 255, 255]

#guard secondsLocal.encodeBufferLE ([⟨-2000⟩] : List (Ticks .localReading .millisecond)) = .ok minusTwo
#guard microsUtc.encodePlain ([⟨-2000⟩] : List (Ticks .utcInstant .nanosecond)) = .ok minusTwo
#guard secondsLocal.encodeBufferLE ([⟨0⟩, ⟨-1999⟩] : List (Ticks .localReading .millisecond)) =
  .error .precisionLoss
#guard microsUtc.encodePlain ([⟨-1999⟩] : List (Ticks .utcInstant .nanosecond)) = .error .precisionLoss
#guard nanosLocal.encodePlain ([⟨9223372036854775808⟩] : List (Ticks .localReading .nanosecond)) =
  .error .outOfRange
#guard nanosLocal.encodePlain ([⟨-9223372036854775809⟩] : List (Ticks .localReading .nanosecond)) =
  .error .outOfRange
#guard microsUtc.encodePlain ([⟨9223372036854775807⟩] : List (Ticks .utcInstant .millisecond)) =
  .error .outOfRange

#guard secondsLocal.decodeBufferLE 0 Bytes.empty = .ok []
#guard secondsLocal.decodeBufferLE 0 minusTwo = .error .trailingBytes
#guard microsUtc.decodePlain 1 (Bytes.ofList [254, 255, 255, 255, 255, 255, 255]) = .error .truncated
#guard microsUtc.decodePlain 1 (minusTwo.push 0) = .error .trailingBytes
#guard microsUtc.decodePlain (2 ^ 64) minusTwo = .error .truncated

#guard ((⟨.second, some ""⟩ : Arrow.Metadata).decodeBufferLE 1 minusTwo).toOption ==
  some ([⟨-2⟩] : List (Ticks .localReading .second))
#guard ((⟨.second, some "Europe/Paris"⟩ : Arrow.Metadata).decodeBufferLE 1 minusTwo).toOption ==
  some ([⟨-2⟩] : List (Ticks .utcInstant .second))

end Silmaril.Formats.ColumnarTimestamp.Wire.Tests
