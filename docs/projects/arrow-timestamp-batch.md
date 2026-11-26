# Checked Arrow IPC Timestamp Schema and batch

`SchemaReader.readMessage` uses its reader-only Timestamp payload arm for
Arrow V5 Schema metadata. It reuses the private FlatBuffers table and slot
validation. The pinned Arrow 26.0.1 IDL assigns Timestamp union tag 10 and
16-bit unit codes 0 through 3 for seconds, milliseconds, microseconds and
nanoseconds. An omitted unit defaults to SECOND. An optional timezone is a
checked UTF-8 string. The reader preserves both an absent slot and an
explicitly present empty string in the normalized field. The legacy primitive
reader keeps its Int32/Utf8 admission profile. The DATE batch and stream readers
use their shared DATE selector and report `unsupportedFieldType` with the
normalized Timestamp unit and timezone.
[Arrow Schema IDL] · [Arrow IPC layout]

`TimestampBatch.bindSchema` admits one flat Timestamp field with little-endian
values. It converts the unit to the existing `ColumnarTimestamp.Arrow.Metadata`
scale. A missing or empty timezone chooses local wall-clock readings. A nonempty
string chooses instants on the Unix scale and retains the exact display annotation.
The adapter has no timezone database or offset interpretation.

`TimestampBatch.readBatch` takes the padded Schema and RecordBatch metadata
slices and the associated body. It checks the declared body length and alignment,
resource limits, one field node, row and null counts, nullability, and ordered
validity and values descriptors. The exact little-endian Int64 wire codec reads
the logical prefix of the values buffer. The existing validity reader applies
bits in slot order and checks their null count against the field node. Values
under null slots do not contribute a tick observation. The caller supplies the
message pairing. Stream and file admission, multiple fields, compressed bodies,
dictionary and nested layouts, and big-endian body decoding are outside this
profile.

## Contracts and fixtures

- `SchemaReader.TimestampUnit.normalize_eq_ok_iff` and `normalize_eq_error_iff`
  specify the omitted default and the exact accepted unit codes.
- `TimestampBatch.bindSchema_iff` identifies the normalized timestamp binding.
- `TimestampBatch.batchView_layout` establishes the node and buffer extents.
- `TimestampBatch.decodeBatch_sound` relates the ordered physical words and
  validity bits to the nullable output, with exact length and null count.
- `TimestampBatch.readBatch_binds` identifies the two supplied metadata messages
  and the bound observation.

The pinned PyArrow 26.0.1 streams cover all units, absent, named and fixed-offset
strings, nullable and required fields, negative ticks and both Int64 endpoints.
Mutated producer metadata distinguishes omitted and explicit SECOND, absent and
present-empty timezone strings, and malformed unit and string payloads. The
checks also cover big-endian admission at the metadata boundary, invalid batch
extents and counts, and the primitive reader's rejection of Timestamp. The DATE
batch and stream checks verify the reported type against the unit and timezone
of each pinned producer fixture. The fixture script pins the complete streams
and mutated metadata by a length-framed SHA-256 and shares the
[wire fixture requirements].

```sh
targets='+Silmaril.Formats.Arrow.Metadata.Thms +Silmaril.Formats.Arrow.Metadata.Tests +Silmaril.Formats.Arrow.TimestampBatch.Thms +Silmaril.Formats.Arrow.DateBatch.Thms +Silmaril.Formats.Arrow.DateBatch.Tests +Silmaril.Formats.Arrow.DateStream.Thms +Silmaril.Formats.Arrow.DateStream.Tests arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/arrow-timestamp-batch/Axioms.lean
python3 -m venv /tmp/arrow-timestamp-batch
/tmp/arrow-timestamp-batch/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/arrow-timestamp-batch/bin/python -I tests/formats/arrow-timestamp-batch/check-fixtures.py
/tmp/arrow-timestamp-batch/bin/python -I scripts/arrow-date-schema-oracle/check.py
/tmp/arrow-timestamp-batch/bin/python -I scripts/arrow-date-stream-oracle/check.py
```

[Arrow Schema IDL]: https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs
[Arrow IPC layout]: https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst
[wire fixture requirements]: ../../tests/formats/columnar-timestamp-wire/requirements.txt
