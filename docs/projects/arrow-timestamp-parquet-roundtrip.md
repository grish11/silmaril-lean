# Arrow TIMESTAMP IPC → Parquet → Arrow IPC

`Parquet.Timestamp.RoundTrip.ipc_roundtrip` composes the checked Arrow-to-Parquet
writer and native Parquet-to-Arrow writer at serialized leaf ordinal one. For
two successful conversions with matching Parquet snapshot and leaf settings,
the input and output IPC readers recover the same typed stream. Its descriptor
contains the field name, nullability, original unit and timezone option. Its
nested lists preserve each signed nullable tick, one footer group per explicit
IPC batch. Consecutive empty batches give distinct groups and batches.
Schema-only IPC gives zero groups and returns to schema-only IPC.
The intermediate observation is recovered by opening the original emitted file
and reading every group in footer order. Equality is of decoded streams.

The domain is one flat little-endian V5 TIMESTAMP field and exact source EOS.
Milliseconds, microseconds and nanoseconds retain their original scale and
full signed Int64 range. An absent timezone maps to local and exact `UTC` maps
to the Parquet adjusted flag and back to `UTC`. Source schema admission refuses
seconds, present-empty timezone, numeric offsets and other labels. The
intermediate file has one modern INT64 TIMESTAMP leaf with uncompressed PLAIN
V1 pages. There is no time coordinate conversion.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/RoundTrip/Thms.lean) ·
[Arrow-to-Parquet profile](arrow-timestamp-to-parquet.md) ·
[Parquet-to-Arrow profile](parquet-timestamp-to-ipc.md)

## Independent limits

- Source admission uses the supplied Arrow `Limits` for schema and record
  metadata, fields, body bytes, rows per batch and batch count. The reverse
  converter also checks the whole IPC source against `maxInputBytes`.
- Parquet output uses the reverse file-byte, group and total-row caps. Its
  Compact schema/footer, level stream, page and framing checks use the supplied
  snapshot and leaf limits. The emitted file must also pass reverse readback
  under those settings.
- The forward converter uses the same snapshot and leaf settings to identify
  that readback. Independently it bounds the actual file length, footer group
  count and declared total rows before pulling any group.
- The Arrow writer uses separate `ObservationLimits`. It checks output batch
  count and aggregate rows and cells, then checks the generated schema and
  record metadata lengths, fields, per-record body extent and rows under its
  own IPC limits. It certifies the complete output with those IPC limits.

The theorem requires success of both calls. Guards exercise a successful
round trip with distinct caps and show that independently tightening the
forward file, group or row caps or the destination batch, aggregate, metadata,
body or row caps can refuse the same certified intermediate.

## Independent readback

The oracle reuses the pinned CPython 3.13.5 and PyArrow 26.0.1 producer set.
Six streams cover all three units with UTC and local descriptors, batches of
sizes `[3, 0, 0, 3]`, and both signed Int64 endpoints at the original unit.
A seventh stream is schema-only. PyArrow and Thrift 0.25.0 check the actual
intermediate Parquet bytes. PyArrow reads the actual final IPC, compares its
field and each batch's raw signed nullable slots with the source, and checks
that reading consumes the entire stream through EOS. Five pinned refusal
inputs exercise early schema rejection and the indexed missing-EOS error.

[Oracle](../../scripts/arrow-timestamp-roundtrip-oracle/check.py) ·
[Lean guards](../../Silmaril/Formats/Parquet/Timestamp/RoundTrip/Tests.lean) ·
[Pinned requirements](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.RoundTrip.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-timestamp-roundtrip-oracle/Axioms.lean
python3 -m venv /tmp/arrow-timestamp-roundtrip
/tmp/arrow-timestamp-roundtrip/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/arrow-timestamp-roundtrip/bin/python -I scripts/arrow-timestamp-roundtrip-oracle/check.py
```
