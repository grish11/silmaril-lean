# Typed TIMESTAMP CSV to a checked Arrow IPC stream

`Arrow.TimestampStream.FromCsv.convert` takes typed UTF-8 CSV, its explicit
one-column TIMESTAMP schema, and a caller-supplied V5 Schema frame. It
returns the exact named database update and complete IPC stream together
after successful emission and readback.
[Entry point](../../Silmaril/Formats/Arrow/TimestampStream/FromCsv/Defs.lean)

The checked reader admits one flat, little-endian, bodyless TIMESTAMP Schema.
The next offset must equal the supplied frame length. The declaration must
match the field name, unit, nullability, and timezone option exactly. Local
coordinates retain an absent or explicitly empty annotation. A nonempty
annotation is kept as opaque text and identifies the existing UTC-instant
interpretation. Bare CSV carries the header and signed tick cells. The
separate declaration supplies timestamp metadata for import.
[Checked IPC profile](arrow-timestamp-stream.md) ·
[Typed timestamp declaration and CSV encoding](arrow-timestamp-to-csv.md)

The adapter decodes CSV using the existing signed Int64 codec with `N` and `T`
cell tags. Nonnullable columns reject null slots. The writer reuses the
caller’s Schema bytes, packs the validity bitmap and exact same-unit
little-endian Int64 values, writes one RecordBatch, and appends explicit EOS.
A header-only input emits one zero-row batch. CSV byte and row limits apply
before parsing and before emission respectively. The IPC limits apply to
schema metadata, rows, batches, body, and record metadata. Before returning
the named result, the adapter reads the complete emitted stream and compares
the exact descriptor and ordered nullable counts.

`checkSchema_sound` proves exact frame consumption and descriptor agreement.
`emit_readback` identifies the supplied Schema, emitted RecordBatch, and EOS
and proves the checked reader recovers the ordered signed nullable counts
at the same schema. `convert_readback` also identifies the exact named insertion
and the decoded CSV rows. Failures return the typed error alone.
[Public laws](../../Silmaril/Formats/Arrow/TimestampStream/FromCsv/Thms.lean)

The oracle pins Schema frames from PyArrow 26.0.1 and typed CSV from
CPython 3.13.5, including all four units, a zoned case with both signed
endpoints, nonnullable and zero-row cases, and a present-empty timezone
annotation. PyArrow independently reads the complete emitted streams. The
controls cover each schema descriptor mismatch, unsupported V4 and
multiple fields, truncated and extra frames, malformed and noncanonical
CSV, nullability, name occupancy, and limits.
[Fixture and oracle](../../scripts/arrow-timestamp-from-csv-oracle/check.py) ·
[Pinned PyArrow and NumPy requirements](../../tests/formats/arrow-ipc/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Arrow.TimestampStream.FromCsv.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.TimestampStream.FromCsv.Checks +Silmaril.Formats.Arrow.TimestampStream.ToCsv.Checks'
python3.13 -m pip install --require-hashes -r tests/formats/arrow-ipc/requirements.txt
python3.13 -I scripts/arrow-timestamp-from-csv-oracle/check.py --out /tmp/silmaril-timestamp-ipc
```
