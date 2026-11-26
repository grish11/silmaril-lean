# Modern Parquet TIMESTAMP schema annotations

`Silmaril.Formats.Parquet.Timestamp.Defs` reads a modern TIMESTAMP annotation
for a selected INT64 leaf in a plaintext Parquet footer. `readFooter` uses the
existing framing and byte budget. `readMetadata` accepts the exact delimited
FileMetaData bytes. Both take a zero-based index into the serialized
`FileMetaData.schema` list, including the root at index zero.

The adapter uses the same bytes for the typed Footer projection and for the
Compact Protocol field traversal. It selects the same ordinal in both views.
The nominated entry must be a non-root INT64 leaf with a repetition marker
and no children. The return value pairs that typed leaf with the checked
`ColumnarTimestamp.Parquet.Metadata` descriptor. Whole-schema validation,
column chunk intervals, and matching a data page to a leaf are caller checks.
The extra structural pass keeps this module independent of Footer projection
and FlatScan changes.

## Supported annotation

The wire rules are pinned to Parquet Format 2.14.0. The reader takes
`LogicalType` from SchemaElement field 10 and requires the singleton
TIMESTAMP union arm 8. It reads the required inline `isAdjustedToUTC` boolean
and the singleton `TimeUnit` arm for MILLIS, MICROS or NANOS. Marker structs
must be empty. Duplicate fields, wrong wire types, missing required fields,
and unsupported or multiple union arms fail. Value payloads must consume
their recorded field extents. [Parquet Thrift IDL] · [TIMESTAMP semantics]

When a deprecated `converted_type` is present with a modern timestamp, it must
be `TIMESTAMP_MILLIS` or `TIMESTAMP_MICROS` as appropriate. NANOS has no
compatible legacy tag. The modern flag determines the interpretation even
when a matching legacy tag is present on a local timestamp. Missing legacy
tags are accepted, as seen in PyArrow's modern local millis and micros output.
A legacy-only tag is outside this profile.

`Binding.decodePlain` feeds an already-delimited little-endian signed INT64
PLAIN slice and its physical present-value count to the verified timestamp
wire adapter. A caller with existing nullable INT64 slots can instead map
`binding.descriptor.decode` inside each `Option`, retaining the established
slot order. This PR covers the annotation and PLAIN values boundary. Page
association, nullable reconstruction, dictionary and delta encoding, INT96,
and timezone resolution belong to their respective layers.

## Checked contracts and fixtures

- `readMetadata_selects` relates the result to the exact selected INT64 leaf
  and annotation at the same ordinal in both views of the footer bytes.
- `readFooter_selects` relates the result to the framed metadata span.
- `annotation_uses_modern` identifies the modern source of the descriptor and
  checks any accompanying legacy tag against the modern unit.
- `Binding.decodePlain_roundtrip` preserves the present value count and
  recovers every accepted PLAIN slice byte for byte.

The pinned PyArrow 26.0.1 fixture contains all six unit and kind combinations
in one file. Neighboring columns differ in annotations and value order, and
unannotated Int32 and Int64 leaves test rejection. The independent reader
checks the typed schema and extracts each uncompressed V1 PLAIN slice. Apache
Thrift 0.25.0 creates additional Compact Protocol fixtures for malformed or
ambiguous annotations and for a valid reordered struct with a matching legacy
tag. The tests use the existing [pinned Python requirements].

```sh
lake build --wfail Silmaril.Formats.Parquet.Timestamp.Defs Silmaril.Formats.Parquet.Timestamp.Thms
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Defs +Silmaril.Formats.Parquet.Timestamp.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-timestamp/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-fixtures
/tmp/parquet-timestamp-fixtures/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-fixtures/bin/python -I tests/formats/parquet-timestamp/check-fixtures.py
```

[Parquet Thrift IDL]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[TIMESTAMP semantics]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#timestamp
[pinned Python requirements]: ../../tests/formats/columnar-timestamp-wire/requirements.txt
