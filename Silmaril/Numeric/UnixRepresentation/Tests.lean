module

import Silmaril.Numeric.UnixRepresentation.Thms
import Silmaril.Numeric.UnixRepresentation.Endpoints
meta import Silmaril.Numeric.UnixRepresentation.Defs

open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.UnixRepresentation

private def justBeforeEpoch : Ticks .utcInstant .nanosecond := ⟨-1⟩

#guard quantize justBeforeEpoch .second .floor = some ⟨-1⟩
#guard quantize justBeforeEpoch .second .trunc = some ⟨0⟩
#guard quantize justBeforeEpoch .second .exact = none
#guard (Timespec.ofTicks justBeforeEpoch).seconds = -1
#guard (Timespec.ofTicks justBeforeEpoch).nanoseconds.val = 999999999
#guard CivilTime.ofTicks justBeforeEpoch = ⟨⟨1969, 12, 31⟩, 23, 59, 59, 999999999⟩

private def error? {α : Type} : Except ConversionError α → Option ConversionError
  | .error error => some error
  | .ok _ => none

#guard error? (WordFormat.uint64.encode justBeforeEpoch .second .floor) = some .outOfRange
#guard (WordFormat.uint64.encode justBeforeEpoch .second .trunc).toOption.map
    WordFormat.uint64.toInt = some 0
#guard error? (WordFormat.uint64.encode justBeforeEpoch .second) = some .precisionLoss
#guard error? (WordFormat.uint64.encode justBeforeEpoch .nanosecond) = some .outOfRange
#guard error? (WordFormat.int32.encode (⟨-2147483649⟩ : Ticks .utcInstant .second) .second) =
    some .outOfRange

private def unsignedMax := WordFormat.uint64.decode .localReading .microsecond 18446744073709551615

#guard unsignedMax.ticks = 18446744073709551615
#guard (WordFormat.uint64.encode unsignedMax .microsecond).toOption.map WordFormat.uint64.toInt =
    some 18446744073709551615
#guard error? (WordFormat.int64.encode unsignedMax .microsecond) = some .outOfRange
#guard error? (WordFormat.uint64.encode unsignedMax .nanosecond) = some .outOfRange

#guard (WordFormat.int32.encode (⟨2147483647999⟩ : Ticks .utcInstant .millisecond)
    .second .floor).toOption.map WordFormat.int32.toInt = some 2147483647
#guard (WordFormat.int32.encode (⟨-2147483648001⟩ : Ticks .utcInstant .millisecond)
    .second .trunc).toOption.map WordFormat.int32.toInt = some (-2147483648)
#guard error? (WordFormat.int32.encode (⟨-2147483648001⟩ : Ticks .utcInstant .millisecond)
    .second .floor) = some .outOfRange
#guard (WordFormat.int64.encode (WordFormat.int32.decode .localReading .second (-2))
    .millisecond).toOption.map WordFormat.int64.toInt = some (-2000)

#guard (⟨⟨1970, 1, 1⟩, 23, 59, 60, 0⟩ : CivilTime).toTicks? .utcInstant = none
#guard (⟨⟨1900, 2, 29⟩, 0, 0, 0, 0⟩ : CivilTime).toTicks? .utcInstant = none
