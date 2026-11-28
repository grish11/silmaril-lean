# Native Arrow V5 TIMESTAMP stream emission

`Arrow.TimestampStream.Writer.emitSchema` emits a complete, bodyless Schema
frame for one flat little-endian TIMESTAMP field. Pass a
`TimestampBatch.Binding` with the field name, nullability, tick unit and
explicit timezone option. The admitted annotations are `none` for local
readings and `some "UTC"` for instants. Other annotations, including a
present-empty string, are rejected with the original option in the error.
All four Arrow units are supported.

The flat layout reuses the existing V5 Message and Schema serializers.
The field carries tag 10, the Timestamp table carries the exact TimeUnit
enum, and the UTC timezone slot references the three-byte UTF-8 string.
The local Timestamp table omits that slot. The Schema preflight checks
the actual padded UTF-8 extent against the IPC limit and signed length
before emitting bytes.

[Arrow V5 Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs) ·
[Arrow IPC layout](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst) ·
[Checked TIMESTAMP reader](arrow-timestamp-stream.md)

`Arrow.TimestampStream.Writer.emit` takes the same binding plus a list of
typed nullable columns. It applies the stream batch and aggregate row/cell
budgets, uses the shared TIMESTAMP record emitter for each column, and
appends one exact EOS. Each record preserves its input batch boundary,
including a zero-row batch. A schema-only stream has no record batches.
Per-record refusals carry the zero-based input batch index. The shared
emitter checks required-field nulls and the signed Int64 payload range.
The CSV adapter calls that emitter through its existing entry point.

## Contracts

- `schemaMetadata_size` identifies the exact padded metadata extent.
- `emitSchema_readback` identifies the exact binding and complete frame
  extent recovered by the normalized reader.
- `emit_wire` relates success to one Schema, the indexed ordered records
  and exact EOS.
- `emit_readback` establishes the original descriptor and every nullable
  signed tick at the same batch and slot.

[Theorem header](../../Silmaril/Formats/Arrow/TimestampStream/Writer/Thms.lean)

## Independent readback

The oracle runs Lean to emit both the standalone Schema and actual stream.
Pinned PyArrow 26.0.1 checks V5 message types, exact Schema extent, unit,
timezone, name and nullability, then reads every signed nullable slot and
batch boundary through EOS. Its eleven cases cover both interpretations
at all four units, signed Int64 endpoints, a UTF-8 field name, required
and optional fields, empty batches, and schema-only streams. The Lean
guards additionally check unsupported annotations, resource limits and
indexed null and range refusal.

[Readback oracle](../../scripts/arrow-timestamp-stream-writer-oracle/check.py) ·
[Lean guards](../../Silmaril/Formats/Arrow/TimestampStream/Writer/Tests.lean) ·
[Pinned wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Arrow.TimestampStream.Writer.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.TimestampStream.Writer.Tests +Silmaril.Formats.Arrow.TimestampStream.FromCsv.Checks'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-timestamp-stream-writer-oracle/Axioms.lean
python3 -m venv /tmp/arrow-timestamp-stream-writer
/tmp/arrow-timestamp-stream-writer/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/arrow-timestamp-stream-writer/bin/python -I scripts/arrow-timestamp-stream-writer-oracle/check.py
```
