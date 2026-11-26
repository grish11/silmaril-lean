# Checked Arrow IPC TIMESTAMP streams

`TimestampStream.read` consumes one complete modern Arrow V5 IPC stream with
one flat little-endian TIMESTAMP field. The first continuation frame supplies
the sole Schema. The [standalone batch binding] retains the field name,
nullability, tick unit and optional timezone, including the difference between
an absent and a present-empty timezone. Missing or empty strings select local
readings. Nonempty strings select instants and retain the exact annotation.
[Arrow Schema IDL] · [Arrow IPC layout]

Each RecordBatch frame supplies the length of its own checked body. The stream
uses the retained schema binding for every batch and keeps one output column per
record in wire order, including an empty list for each zero-row batch. A
schema-only stream has an empty batch list. The reader requires an explicit
modern EOS at the exact end of the input and enforces the existing per-message
limits and stream batch budget. Errors identify the failing stage and, after
the Schema, its zero-based batch index. Framing, metadata, body and value errors
retain their original typed causes.

The stream reader uses the existing framing functions, normalized schema reader
and TIMESTAMP batch decoder. The primitive and DATE readers retain their own
profiles. File admission, writing, nested and dictionary schemas, compression,
big-endian bodies and timezone resolution are outside this profile.

## Public contracts

- `readSchema_iff` relates the returned binding to the checked first frame.
- `readBatch_iff` identifies the record metadata, its declared body, the
  decoded slots and the next frame boundary. The batch decoder's
  `decodeBatch_sound` relates those slots to exact words and validity bits.
- `readBatches_iff` establishes wire order through exact EOS within the batch
  budget. The relation includes every record, even when its column is empty.
- `read_iff` combines the schema and suffix contracts for a complete stream.

## Verification

The pinned PyArrow 26.0.1 oracle covers all four units, named and fixed-offset
annotations, local readings, a present-empty timezone, mixed nulls, signed
endpoints, a required field, and empty records. Checked refusals include
truncated metadata and bodies, missing EOS, trailing bytes, malformed metadata,
an inconsistent validity bitmap, a second schema, and a batch limit reached at
an empty record. Primitive and DATE readers still reject these TIMESTAMP schemas
with their existing typed errors.

```sh
lake build --wfail Silmaril.Formats.Arrow.TimestampStream.Thms
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.TimestampStream.Thms +Silmaril.Formats.Arrow.DateStream.Thms +Silmaril.Formats.Arrow.DateStream.Tests arrow_ipc_metadata_tests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/arrow-timestamp-stream/Axioms.lean
python3 -m venv /tmp/arrow-timestamp-stream
/tmp/arrow-timestamp-stream/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/arrow-timestamp-stream/bin/python -I tests/formats/arrow-timestamp-stream/check-fixtures.py
```

[standalone batch binding]: arrow-timestamp-batch.md
[Arrow Schema IDL]: https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs
[Arrow IPC layout]: https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst
