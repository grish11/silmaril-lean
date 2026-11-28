# Bounded Parquet TIMESTAMP data-page slots

`Silmaril.Formats.Parquet.Timestamp.Page.decode` takes a checked timestamp
binding, the effective schema levels, the column codec, a checked `Page.Header`,
and one exact compressed body. Limits bound the existing scalar-page decoder.
Each output slot has the descriptor's tick unit and epoch interpretation.
Local and UTC-adjusted values use their existing distinct types.

`leafLevels?` admits an INT64 leaf with no children and required or optional
repetition. The effective levels supplied by the caller must match `(0, 0)`
for required or `(0, 1)` for optional. The adapter takes sizes, encoding,
counts and version-specific fields from the header and calls
`ScalarPage.decode .int64`. That decoder checks body extent, compression,
levels, counts and exact PLAIN consumption. The adapter then interprets each
present signed Int64 in order and preserves each null slot.

The profile admits the bounded PLAIN V1 and V2 paths supported by ScalarPage.
The caller associates the binding, effective levels, header, column codec,
and body to the same page. File-to-page association, page checksum validation,
nested or repeated layouts, and dictionary or delta encodings are outside this
profile. A scanner can pass already-associated inputs through this boundary.
[Parquet Thrift IDL] · [PLAIN encoding] · [TIMESTAMP semantics]

## Contracts and fixtures

- `parameters_sound` ties the scalar parameters to the checked leaf layout
  and header.
- `decode_eq_ok_iff` identifies the pointwise mapping over the checked
  physical Int64 slots.
- `decode_sound` establishes exact body size, the checked null mask, the
  original order, and equality of the present signed tick counts.
- `decode_counts` checks the declared slot count and the V2 present count.

The pinned PyArrow 26.0.1 files cover uncompressed V1 and V2 and Snappy V2.
Each contains all three units in both epochs with mixed nulls and negative
counts, plus required and all-null columns. Apache Thrift 0.25.0 delimits the
page headers and bodies for the oracle. PyArrow independently reads back the
ordered slots. Lean checks 24 pages and 13 malformed inputs, including
mismatched levels, body extent, count caps, encoding and V2 counts. The
oracle pins the length-framed SHA-256 of the three files and shares the
[wire fixture requirements].

```sh
lake build --wfail Silmaril.Formats.Parquet.Timestamp.Page.Defs Silmaril.Formats.Parquet.Timestamp.Page.Thms
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Page.Defs +Silmaril.Formats.Parquet.Timestamp.Page.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-timestamp-page/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-page
/tmp/parquet-timestamp-page/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-page/bin/python -I tests/formats/parquet-timestamp-page/check-fixtures.py
```

[Parquet Thrift IDL]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[PLAIN encoding]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#plain-plain--0
[TIMESTAMP semantics]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#timestamp
[wire fixture requirements]: ../../tests/formats/columnar-timestamp-wire/requirements.txt
