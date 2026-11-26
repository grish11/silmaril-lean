# Arrow TIMESTAMP IPC to modern Parquet TIMESTAMP

`Parquet.Timestamp.FromIpc.convert` accepts a single flat little-endian
TIMESTAMP field in an Arrow V5 IPC stream. It selects millis, micros or
nanos directly from that field. The exact absent timezone selects a local
reading and `some "UTC"` selects an instant. Seconds, a present-empty
timezone, numeric offsets and other labels are refused when binding the
checked Schema layer. Successful conversion requires exact source EOS.

The output is a Parquet file with one flat INT64 leaf and the modern
TIMESTAMP annotation. Its `isAdjustedToUTC` flag reflects the accepted
source interpretation. Millis and micros also carry the required matching
legacy unit tag. Every explicit Arrow batch becomes one footer group with
one uncompressed PLAIN V1 page, even for an empty batch. A schema-only
stream emits a zero-group file. The field name, nullability, unit, and
signed counts carry through unchanged. Local and UTC payloads stay on
their original epoch scales.

[Arrow V5 Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs) ·
[Parquet TIMESTAMP compatibility rules](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#timestamp) ·
[Parquet 2.14.0 Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

The source byte cap and IPC frame limits apply while reading. Output
admission checks group, total row, schema and page budgets before forming
the data bodies. The writer measures each page and bounds the Compact
footer against the remaining file budget. It uses the existing group-list
serializer with the INT64 type code and a TIMESTAMP leaf serializer.
The existing INT32 and DATE calls continue to use type code 1.

The emitted file is released after the checked TIMESTAMP leaf reader
recovers the original descriptor and its ordered groups. Writer preflight
and this certification use the same supplied snapshot and leaf limits.
The profile covers modern INT64 only. INT96, calendar rebasing, compression
and multiple projected fields are separate profiles.

## Contracts

- `descriptor_exact` preserves unit, timezone policy and epoch interpretation.
- `readSource_refusal` establishes early descriptor refusal after the checked
  Schema, regardless of subsequent record bodies.
- `readSource_exact` relates an admitted source to the existing complete IPC
  reader.
- `convert_readback` identifies the exact accepted IPC source and the
  certified Parquet leaf, declared counts, and ordered nullable slot lists.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/FromIpc/Thms.lean)

## Independent readback

The pinned PyArrow 26.0.1 producer supplies six streams covering all
three units and both interpretations, plus a schema-only stream. Each
nonempty stream has four batches with sizes `[3, 0, 0, 3]`, including
signed Int64 endpoints. PyArrow reads the actual Lean-emitted Parquet
and checks the field and each group separately. Thrift 0.25.0 checks
physical type, modern and legacy tags, page extents, definition levels and
the exact little-endian words. The adjacent empty groups have distinct
positive-sized framed page intervals.

Four unsupported descriptor inputs omit EOS to check that refusal occurs
at Schema admission. A fifth control checks the original indexed error
for an admitted stream with missing EOS. Lean guards cover exact signed
readback, zero groups, consecutive empty groups, and resource limits.

[Writer and readback oracle](../../scripts/arrow-timestamp-to-parquet-oracle/check.py) ·
[Lean guards](../../Silmaril/Formats/Parquet/Timestamp/FromIpc/Tests.lean) ·
[Pinned wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.FromIpc.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.FromIpc.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-timestamp-to-parquet-oracle/Axioms.lean
python3 -m venv /tmp/arrow-timestamp-to-parquet
/tmp/arrow-timestamp-to-parquet/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/arrow-timestamp-to-parquet/bin/python -I scripts/arrow-timestamp-to-parquet-oracle/check.py
```
