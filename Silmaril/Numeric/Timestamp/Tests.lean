module

import Silmaril.Numeric.Timestamp.Defs
meta import Silmaril.Numeric.Timestamp.Defs

namespace Silmaril.Numeric.Timestamp

private def error? : Except ConversionError Int64 → Option ConversionError
  | .error error => some error
  | .ok _ => none

-- All four units denote the same offset one second before the epoch.
#guard (Ticks.ofInt64 .utcInstant .second (-1)).denote.ticks == -1000000000
#guard (Ticks.ofInt64 .utcInstant .millisecond (-1000)).denote.ticks == -1000000000
#guard (Ticks.ofInt64 .utcInstant .microsecond (-1000000)).denote.ticks == -1000000000
#guard (Ticks.ofInt64 .utcInstant .nanosecond (-1000000000)).denote.ticks == -1000000000

-- Exact coarsening keeps the epoch kind. A fractional negative tick is rejected.
#guard (Ticks.ofInt64 .localReading .microsecond (-1234000)).rescale .millisecond ==
    some (⟨-1234⟩ : Ticks .localReading .millisecond)
#guard ((Ticks.ofInt64 .utcInstant .second (-1)).toInt64 .millisecond).toOption == some (-1000)
#guard error? ((Ticks.ofInt64 .localReading .microsecond (-1234001)).toInt64 .millisecond) ==
    some .precisionLoss
#guard error? ((Ticks.ofInt64 .utcInstant .nanosecond (-1)).toInt64 .second) == some .precisionLoss

-- Both endpoints are accepted and their signed values survive unchanged.
#guard (((⟨-9223372036854775808⟩ : Ticks .utcInstant .nanosecond).toInt64 .nanosecond).toOption.map
    Int64.toInt) == some (-9223372036854775808)
#guard (((⟨9223372036854775807⟩ : Ticks .utcInstant .nanosecond).toInt64 .nanosecond).toOption.map
    Int64.toInt) == some 9223372036854775807
#guard error? ((⟨-9223372036854775809⟩ : Ticks .utcInstant .nanosecond).toInt64 .nanosecond) ==
    some .outOfRange
#guard error? ((⟨9223372036854775808⟩ : Ticks .utcInstant .nanosecond).toInt64 .nanosecond) ==
    some .outOfRange

-- Range is checked on the target count, after exact scaling with unbounded integers.
#guard error? ((Ticks.ofInt64 .utcInstant .millisecond Int64.minValue).toInt64 .nanosecond) ==
    some .outOfRange
#guard error? ((Ticks.ofInt64 .utcInstant .millisecond Int64.maxValue).toInt64 .nanosecond) ==
    some .outOfRange
#guard ((Ticks.ofInt64 .utcInstant .millisecond Int64.minValue).toInt64 .millisecond).toOption ==
    some Int64.minValue
#guard ((⟨9223372036854775807000⟩ : Ticks .localReading .nanosecond).toInt64 .microsecond).toOption ==
    some Int64.maxValue

end Silmaril.Numeric.Timestamp
