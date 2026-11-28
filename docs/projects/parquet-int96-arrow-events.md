# Exact Arrow TIMESTAMP events from mixed INT96

`Silmaril.Formats.Parquet.Int96.Mixed.File.Events.readAll` opens one selected
flat INT96 leaf using the checked mixed-file profile. The caller chooses both
the proleptic UTC or local interpretation and the Arrow tick unit. The one
Arrow TIMESTAMP field retains the bound name and required or optional layout.
The UTC policy gives the canonical annotation `some "UTC"`. The local
policy gives an absent annotation.

The existing INT96 payload API already supplies the Gregorian coordinates
and the mathematical nanosecond denotation. This adapter starts with the
checked file reader's nanoseconds and reuses `Ticks.toInt64` for seconds,
millis, micros and nanos. Each present value must convert exactly and fit a
signed Int64. Precision loss and range overflow keep their distinct errors.
The accepted word is interpreted using the chosen Arrow metadata so its
nanosecond denotation stays exact. Calendar rebasing, timezone lookup and
public IPC writing are separate profiles.

[INT96 word and Gregorian laws](parquet-int96.md) ·
[Exact tick narrowing](timestamp.md) ·
[Mixed selected-leaf source](parquet-int96-mixed-file.md) ·
[Typed modern TIMESTAMP events](parquet-timestamp-events.md)

## Order and errors

The adapter uses the existing typed Arrow event reader over indexed footer
groups. It reads and checks a complete source group before narrowing any of
its slots. Any source error takes the original cause with the group index.
Narrowing walks the successfully decoded slots in order and adds the exact
group and logical slot index to the first precision or range failure. A
failure publishes exactly the earlier complete batches. Each successful
group contributes one batch, including a successfully framed zero-row group.

## Contracts

- `metadata_exact` and `schema_field` establish unit, epoch interpretation,
  annotation, selected name and nullability.
- `narrowSlot_exact` and `narrowSlot_error_iff` tie accepted payloads and
  refusals to the exact scalar contract. `narrowSlots_exact` and
  `narrowSlots_first_error` preserve nullable order and logical error index.
- `batch_slots` preserves the entire narrowed group. `slotsAt_source_error`
  and `slotsAt_after_read` describe the phase order for the selected group.
  `readAll_reference` and `readAll_first_error` establish the ordered trace
  and exact batch prefix on failure.

[Theorem header](../../Silmaril/Formats/Parquet/Int96/Mixed/File/Events/Thms.lean)

## Independent fixtures and readback

The oracle pins prior PyArrow 26.0.1 mixed V1/V2 producers and a required
dictionary V1 producer with signed Int64 nanosecond endpoints. The V2
producer's microsecond counts reach beyond the signed nanosecond range.
Thrift 0.25.0 derives a pinned empty-group control by adding one valid
zero-entry dictionary and a zero-slot V2 data page at footer ordinal 1.
PyArrow independently reads its four groups. A second pinned V2 derivative
increments one PLAIN word by a nanosecond, causing inexact microsecond
narrowing at group 1, logical slot 10. Lean guards also check both kinds of
error ordering using the existing corrupt files.

The test harness uses PyArrow-produced Schema frames and the existing Lean
TIMESTAMP record emitter to serialize the actual event batches. PyArrow
then reads the Lean-produced IPC and compares field name, nullability, unit,
timezone, and every ordered nullable signed payload to its Parquet read.
The six readbacks cover both interpretations, mixed V1 nanos, mixed V2
micros with batch sizes `[24, 0, 24, 24]`, and the required V1 endpoints.

[Oracle and SHA-256 pins](../../scripts/parquet-int96-arrow-events/check-fixtures.py) ·
[Test-only IPC emitter](../../scripts/parquet-int96-arrow-events/Emit.lean) ·
[Lean guards](../../Silmaril/Formats/Parquet/Int96/Mixed/File/Events/Tests.lean) ·
[Pinned wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int96.Mixed.File.Events.Tests +Silmaril.Formats.Arrow.TimestampStream.FromCsv.Defs
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int96.Mixed.File.Events.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-int96-arrow-events/Axioms.lean
python3 -m venv /tmp/parquet-int96-arrow-events
/tmp/parquet-int96-arrow-events/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-int96-arrow-events/bin/python -I scripts/parquet-int96-arrow-events/check-fixtures.py
```
