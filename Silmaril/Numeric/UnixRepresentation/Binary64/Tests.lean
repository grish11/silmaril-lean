module

import Silmaril.Numeric.UnixRepresentation.Binary64.Thms
meta import Silmaril.Numeric.UnixRepresentation.Binary64.Defs

open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.UnixRepresentation.Binary64
open Silmaril.Numeric.Ieee754.RationalRounding (overflowThreshold)

private def error? {α : Type} : Except Error α → Option Error
  | .error error => some error
  | .ok _ => none

private def seconds (n : Int) : Ticks .utcInstant .second := ⟨n⟩

-- Both signed zeros decode to the epoch and the epoch encodes as +0.
#guard (decode .utcInstant (F64.ofBits 0) .second .nanosecond).toOption = some ⟨0⟩
#guard (decode .utcInstant (F64.ofBits 0x8000000000000000) .second .nanosecond).toOption =
    some ⟨0⟩
#guard (encodeExact (seconds 0) .nanosecond).toOption.map F64.bits = some 0

-- The smallest subnormals retain their signs in the rational count. They are
-- fractional even in nanoseconds, where floor and truncation diverge below zero.
#guard decodeCount? (F64.ofBits 1) .nanosecond .nanosecond = some ((2 : ℚ) ^ (-1074 : Int))
#guard decodeCount? (F64.ofBits 0x8000000000000001) .nanosecond .nanosecond =
    some (-(2 : ℚ) ^ (-1074 : Int))
#guard error? (decode .utcInstant (F64.ofBits 1) .second .nanosecond) = some .precisionLoss
#guard (decode .utcInstant (F64.ofBits 0x8000000000000001) .second .nanosecond .floor).toOption =
    some ⟨-1⟩
#guard (decode .utcInstant (F64.ofBits 0x8000000000000001) .second .nanosecond .trunc).toOption =
    some ⟨0⟩

#guard error? (decode .utcInstant (F64.ofBits 0x7ff0000000000000) .second .second .floor) =
    some .nonfinite
#guard error? (decode .utcInstant (F64.ofBits 0xfff0000000000000) .second .second) = some .nonfinite
#guard error? (decode .utcInstant (F64.ofBits 0x7ff8000000000000) .second .second .trunc) =
    some .nonfinite

-- Exact unit scaling, then one RNE conversion for a decimal fraction.
#guard (encodeExact (⟨-125⟩ : Ticks .localReading .millisecond) .second).toOption.map F64.bits =
    some 0xbfc0000000000000
#guard (decode .localReading (F64.ofBits 0xbfc0000000000000) .second .microsecond).toOption =
    some ⟨-125000⟩
#guard (encodeRne (⟨1⟩ : Ticks .utcInstant .millisecond) .second).toOption.map F64.bits =
    some 0x3f50624dd2f1a9fc
#guard error? (encodeExact (⟨1⟩ : Ticks .utcInstant .millisecond) .second) = some .precisionLoss

-- At 2^53 the next spacing is two. The first odd integer ties down,
-- and the next odd integer ties up to the even encoding.
#guard (encodeExact (seconds (2 ^ 53)) .second).toOption.map F64.bits = some 0x4340000000000000
#guard (encodeExact (seconds (-(2 ^ 53))) .second).toOption.map F64.bits = some 0xc340000000000000
#guard (encodeRne (seconds (2 ^ 53 + 1)) .second).toOption.map F64.bits = some 0x4340000000000000
#guard (encodeRne (seconds (2 ^ 53 + 3)) .second).toOption.map F64.bits = some 0x4340000000000002
#guard error? (encodeExact (seconds (2 ^ 53 + 1)) .second) = some .precisionLoss
#guard (encodeExact (seconds (2 ^ 53 + 2)) .second).toOption.map F64.bits = some 0x4340000000000001

#guard (encodeRne (seconds (overflowThreshold.num - 1)) .second).toOption.map F64.bits =
    some 0x7fefffffffffffff
#guard error? (encodeRne (seconds overflowThreshold.num) .second) = some .overflow
#guard error? (encodeExact (seconds (-overflowThreshold.num)) .second) = some .overflow
