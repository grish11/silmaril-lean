# Checked Arrow IPC DATE batch binding

`Silmaril.Formats.Arrow.DateBatch.decode` reads two padded V5 message metadata
slices and one record body slice. The Schema must contain exactly one ordered
field with Arrow's DATE union tag 8. The normalized DAY unit selects signed
little-endian Date32 epoch days. The normalized MILLISECOND unit, including
the omitted DateUnit default, selects signed little-endian Date64 epoch
milliseconds and requires exact whole days for present values. Schema
nullability and byte order are passed to the existing DATE value decoder.
Big endian is rejected by that decoder. The record must declare the supplied
body length in bytes, with a multiple-of-eight body length. The checked DATE
value decoder validates the field node, bitmap, and value-buffer spans.
[Arrow 26.0.1 Schema.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)
· [Pinned Arrow IPC specification](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)
· [DATE buffer profile](arrow-date-values.md)

`DateBatch.decode_iff` characterizes success by the sole normalized schema
field, record message and body length, checked bitmap and data buffers, and
the ordered nullable slot relation. `DateBatch.decode_counts` gives the exact
record row count and field-node null count. Schema, record, body-length and
value-decoding errors retain their stage in the result.
[Public theorem headers](../../Silmaril/Formats/Arrow/DateBatch/Thms.lean)

The caller pairs each record and its body with the corresponding Schema.
Envelope handling, stream ordering, multiple fields or batches, file
footers, Timestamp, and writing are outside this API.

## Verification

The Lean fixtures extract both messages and the body from each of two
PyArrow-produced IPC streams. The oracle regenerates those same streams with
pinned CPython 3.13.5 and PyArrow 26.0.1, verifies the stream and component
hashes, and compares the observed DATE results against PyArrow. Both streams
contain a negative epoch date, a null, a leap day, and the epoch. Controlled
inputs exercise schema and record admission, wrong field count and type,
Big endian, a null in a required field, a Date64 remainder, and body-length
mismatch and alignment.
[Fixture manifest](../../scripts/arrow-date-schema-oracle/fixtures.json)
· [Lean regressions](../../Silmaril/Formats/Arrow/DateBatch/Tests.lean)

```sh
targets='+Silmaril.Formats.Arrow.DateBatch.Thms +Silmaril.Formats.Arrow.DateBatch.Tests +Silmaril.Formats.Arrow.Metadata.Tests +Silmaril.Formats.Arrow.DateValues.Tests arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/arrow-date-schema-oracle/check.py
```

Use `--pyarrow-path` when the pinned wheel was unpacked outside the Python
environment.
