# Exact fixed-point timestamps

`Silmaril.Numeric.Timestamp.Defs` models signed, unbounded epoch-relative tick
counts at second, millisecond, microsecond and nanosecond precision. `Ticks.denote`
multiplies the count by the nanoseconds per tick using exact integer arithmetic.
For example, −1 millisecond denotes −1,000,000 nanoseconds relative to the
same epoch.

The kind index distinguishes a UTC instant on the Unix timescale, with epoch
1970-01-01 00:00:00 UTC, from a local wall-clock reading relative to local
1970-01-01 00:00:00. The local scale uses uniform 86,400-second days. The model
has no leap-second or daylight-saving adjustments. Denotation and rescaling
preserve the kind. A signed 64-bit payload carries only a count. Its kind and
unit must be supplied separately when interpreting it, and recovering an
instant from a local reading would require additional information.

`Ticks.rescale` succeeds when the offset is an integral number of destination
ticks, including for negative offsets. `Ticks.toInt64` first checks exactness
and reports `precisionLoss` for fractional destination ticks. It then reports
`outOfRange` if the destination count is outside [−2⁶³, 2⁶³ − 1]. The bounds are
inclusive. All intermediate arithmetic uses unbounded integers. `Ticks.ofInt64`
accepts every signed 64-bit count paired with a kind and unit.

`Silmaril.Numeric.Timestamp.Thms` characterizes successful conversions by
equality of exact denotations. An exact rescaling can be reversed, and a
successful unit conversion of a signed 64-bit payload can be reversed to the
original payload in its original unit.

The shared model covers the numeric units and the instant/local distinction in
the following upstream specifications. Arrow allows all four units. Parquet
`TIMESTAMP` allows milliseconds, microseconds and nanoseconds and distinguishes
interpretations with `isAdjustedToUTC`.

- Apache Arrow 22.0.0, `TimeUnit` and `Timestamp` in `format/Schema.fbs`.
  [Pinned schema](https://github.com/apache/arrow/blob/5aeb5f217f1ba39c428c9b481f393bd37097f69e/format/Schema.fbs#L256-L397)
- Apache Parquet Format 2.12.0, `TIMESTAMP` in `LogicalTypes.md`.
  [Pinned specification](https://github.com/apache/parquet-format/blob/7e401bf1c970488457670f17cf103bd03acea9c1/LogicalTypes.md#L348-L465)

Calendar and ISO 8601 conversion, Arrow timezone metadata mapping, Parquet
INT96, and Arrow and Parquet wire codecs are follow-up work. The core leaves
format-specific unit and metadata validation to those adapters.

Build the public headers, proofs and regression cases with the pinned Lean
toolchain from the repository root.

```sh
lake build --wfail +Silmaril.Numeric.Timestamp.Thms +Silmaril.Numeric.Timestamp.Tests
```
