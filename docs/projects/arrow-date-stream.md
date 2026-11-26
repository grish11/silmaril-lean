# Checked single-column Arrow DATE streams

`Silmaril.Formats.Arrow.DateStream.read` reads a finite, in-memory Arrow IPC
V5 stream containing one flat DATE field. It reads the first framed Schema
once and uses the normalized field's name, nullability, and unit for every
batch. Modern continuation framing and explicit EOS are required. A record's
metadata declares the checked body slice and determines the next aligned
frame boundary. The result preserves batch boundaries, including empty
batches, and returns the ordered nullable Gregorian dates within each batch.
[Pinned Arrow IPC specification](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)
· [Pinned Schema.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)

The reader admits little-endian Date32 epoch days and Date64 epoch
milliseconds that represent exact whole days. It uses the same envelope,
RecordBatch metadata and body readers as the Int32/UTF-8 stream path, plus
the DATE slot decoder. The admitted schema can have zero record batches.
Per-message metadata/body/row limits apply, and `Limits.batches` bounds
the number of record batches. Mixed or multiple fields, legacy framing,
files, writing, and Timestamp are outside this profile.
[Schema and value binding](arrow-date-batch.md)

An error identifies the source or schema stage, or the batch stage and
its zero-based index. The first failed batch or expected EOS ends the
operation with an error. For example, a truncated body and a Date64
remainder both identify their batch and preserve their underlying causes.

`readSchema_iff` and `readBatch_iff` characterize the checked Schema and
record slices. `readBatches_iff` and `read_iff` characterize the ordered
observation through exact EOS. `readBatches_error_iff` and
`read_batch_error_iff` characterize indexed failures after the preceding
batches have decoded. [Public theorems](../../Silmaril/Formats/Arrow/DateStream/Thms.lean)

## Verification

Pinned CPython 3.13.5 and PyArrow 26.0.1 supply full Date32 and Date64 streams.
Both have a nullable negative epoch date, an empty middle batch, a leap
day, and the epoch. Fixtures also cover a schema-only stream, a batch
budget, missing and trailing EOS bytes, repeated schema, invalid record
metadata, a truncated body, and a late Date64 remainder. The legacy reader
still rejects the DATE schema while its existing native regressions pass.
[Fixture manifest](../../scripts/arrow-date-stream-oracle/fixtures.json)

```sh
targets='+Silmaril.Formats.Arrow.DateStream.Thms +Silmaril.Formats.Arrow.DateStream.Tests +Silmaril.Formats.Arrow.DateBatch.Thms +Silmaril.Formats.Arrow.DateBatch.Tests +Silmaril.Formats.Arrow.Metadata.Tests +Silmaril.Formats.Arrow.DateValues.Tests arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/arrow-date-stream-oracle/check.py
```

Use `--pyarrow-path` when the pinned wheel was unpacked outside the Python
environment.
