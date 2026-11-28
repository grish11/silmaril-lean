# Unix timestamp representations

The representation layer uses [Timestamp ticks](timestamp.md) relative to
1970-01-01, in seconds, milliseconds, microseconds or nanoseconds. The caller
supplies the unit and epoch kind. The Gregorian adapter uses uniform days of
86,400 seconds, with clock seconds in 0–59. UTC/TAI conversion, leap-second
tables, smear, clock maps, and ISO text are separate interfaces.

## Integer words and civil fields

`WordFormat.decode` interprets every `Int32`, `Int64`, and `UInt64` payload as
an unbounded tick count in the supplied kind and unit. `WordFormat.encode`
first calls `quantize`, then checks the destination count against the word's
closed interval. The intervals are [−2³¹, 2³¹−1], [−2⁶³, 2⁶³−1], and
[0, 2⁶⁴−1], respectively. The signed 64-bit exact conversion agrees with
`Timestamp.Ticks.toInt64`.

- `.exact` rejects a fractional destination tick with `.precisionLoss` before
  checking range. A successful exact conversion preserves the offset and can
  be reversed across word formats and units.
- `.floor` takes the greatest count at or below the offset. The discarded
  offset is nonnegative and strictly smaller than one destination tick.
- `.trunc` goes toward zero. The discarded offset has magnitude strictly
  smaller than one destination tick and follows the sign of the input.

For example, converting −1 ns to an unsigned seconds word gives
`.precisionLoss` under exact conversion, `.outOfRange` under floor, and a
payload of zero under truncation. Signed seconds can represent the floored
count −1.

`Timespec.ofTicks` splits any tick count into unbounded floor seconds and a
nanosecond field in [0, 10⁹). `Timespec.toTicks` reconstructs the exact
nanosecond denotation. In particular, −1 ns splits as
(−1 s, 999,999,999 ns). This describes normalized fields independently of
any C ABI's word widths. `CivilTime.ofTicks` and `CivilTime.toTicks?` compose
this split with Gregorian epoch-day decoding and checked encoding. The civil
encoder checks the Gregorian date and the hour, minute, and second ranges.

| Format | Signed tick count | Civil date and time |
| --- | ---: | --- |
| Int32 seconds, minimum | −2147483648 | 1901-12-13 20:45:52 |
| Int32 seconds, maximum | 2147483647 | 2038-01-19 03:14:07 |
| Int32 seconds, first positive overflow | 2147483648 | 2038-01-19 03:14:08 |
| Int64 nanoseconds, minimum | −9223372036854775808 | 1677-09-21 00:12:43.145224192 |
| Int64 nanoseconds, maximum | 9223372036854775807 | 2262-04-11 23:47:16.854775807 |

The Lean endpoint theorems give the actual word values, civil encode/decode
equalities, and the range error at the first second above the Int32 maximum.
[Integer and civil laws](../../Silmaril/Numeric/UnixRepresentation/Thms.lean) ·
[Endpoint theorems](../../Silmaril/Numeric/UnixRepresentation/Endpoints.lean)

## Binary64

`Binary64.decodeCount?` uses the IEEE model's exact `F64.toRat?` accessor and
scales the rational to the requested tick unit. Subnormals keep their exact
dyadic value. Both signed zeros give zero. `Binary64.decode` applies exact,
floor, or truncation to the scaled count and returns unbounded ticks. NaNs and
infinities give `.nonfinite` under all three policies. The floor and truncation
bounds are in destination ticks.

`Binary64.encodeRne` scales the integer source to the exact rational count in
the payload unit, then calls the repository's signed nearest-even converter
once. At or above the overflow midpoint 2¹⁰²⁴ − 2⁹⁷⁰ in magnitude, it returns
`.overflow`. A successful output is finite. The epoch encodes as positive
zero. `Binary64.encodeExact` additionally requires the decoded rational to
equal the input count, with `.precisionLoss` for finite changes. Exact
round trips recover the ticks or the finite rational value, respectively.
The numerical round trip identifies the two signed-zero encodings.

The exact-encoding theorem covers every integral count in the payload unit
from −2⁵³ through 2⁵³. Finer-to-coarser scaling can produce a non-dyadic
fraction, for example 1 ms encoded in seconds. Above 2⁵³, some integers are
still representable. For successful RNE encoding the error is at most half
the spacing in the binary64 interval bracketing the absolute input count,
in payload units. That is the subnormal spacing 2⁻¹⁰⁷⁴ at the bottom of
the format and uses the virtual upper neighbor 2¹⁰²⁴ at the top. Below
2⁵³ payload units in magnitude, the spacing is at most one and the error is
at most half a payload unit. The encoder's input grid has minimum nonzero
magnitude 10⁻⁹ in payload units. Subnormal interchange values can still
be supplied to the decoder.
[Binary64 laws](../../Silmaril/Numeric/UnixRepresentation/Binary64/Thms.lean)

## References and checks

- POSIX.1-2024, Base Definitions §4.19, seconds since the Epoch, and
  `<time.h>` for `timespec`.
  [Epoch](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap04.html#tag_04_19) ·
  [time.h](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/time.h.html)
- IEEE 754-2019, binary interchange formats and rounding direction
  attributes. [Standard](https://standards.ieee.org/ieee/754/6210/)

```sh
lake build --wfail +Silmaril.Numeric.UnixRepresentation.Tests \
  +Silmaril.Numeric.UnixRepresentation.Binary64.Tests
```
