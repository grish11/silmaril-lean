# Unix clock, zone, and codec integration

`Silmaril.Numeric.UnixInterop.Defs` defines the exact handoff. The public
results are in `Silmaril.Numeric.UnixInterop.Thms`.

## Physical time to local civil time

`readWall?` takes a physical instant in a `UnixClock.Convention`'s support.
The clock produces nominal seconds. `exactNanoseconds?` accepts them precisely
when multiplying by 10⁹ gives an integer, including negative counts. On that
grid the signed nanosecond timestamp is unique. The zone evaluates its offset
and validity horizon at that exact timestamp. `readCivil?` then reads the local
wall timestamp as Gregorian fields on uniform 86,400-second days.

`physicalCandidates` unions the clock fibers of all nominal candidates returned
by the zone. Membership is equivalent to having a supported physical input
that produces the specified wall reading. For a civil reading, `readCivil_eq_some_iff`
also requires its Gregorian fields and nanoseconds of day to encode a valid wall
reading. A zone gap or a missing clock fiber can leave the inverse empty. Zone
folds and clock repeats can both contribute multiple instants. The regression
constructs a zone with two nominal candidates at local midnight, one of which
has a two-element clock fiber, and proves the resulting three physical
preimages are exactly 0, 1, and 2 SI seconds.

The grid adapter is a noncomputable function on mathematical reals. An off-grid
sample returns `none`. A separate quantizing API would have to specify which side
of a zone transition the selected timestamp falls on.
[Clock model](unix-clock.md) · [Zone model](time-zone-rules.md)

## Encoded clock comparisons

`wordFloor_discrepancy` and `binary64Rne_discrepancy` compare two clock readings
at the same physical instant on the intersection of their domains. Each
reading must have an exact nanosecond stamp and a successful encoding with its
chosen format and unit. The bounds add the two representation errors to the
absolute clock discrepancy, all in seconds.

- Integer floor supports the signed 32-bit, signed 64-bit and unsigned 64-bit
  word formats. Each decoded count is below or equal to the source reading and
  loses strictly less than one destination tick. The regression compares
  signed 64-bit seconds with signed 64-bit milliseconds.
- Binary64 uses finite round-to-nearest, ties-to-even. The exact rational value
  of the finite payload and half its input-local ULP are both multiplied by the
  length of its payload tick. The comparison concerns the exact value denoted
  by the payload. A subsequent decode to an integer tick grid can add a further
  rounding error.

These pointwise bounds concern the nominal coordinates before applying zone
rules. A zone offset jump can change the local discrepancy if the two nominal
readings straddle its transition. The analytic clock bounds can supply the
clock term whenever their hypotheses apply to the shared physical instant.
[Representation model](unix-representation.md)

## Checks

```sh
lake build --wfail +Silmaril.Numeric.UnixInterop.Thms +Silmaril.Numeric.UnixInterop.Tests
make check CHECK_TARGETS='+Silmaril.Numeric.UnixInterop.Thms +Silmaril.Numeric.UnixInterop.Tests'
```
