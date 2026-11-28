# Checked Parquet DATE row groups

`Silmaril.Formats.Parquet.Date.readGroup` reads one selected row group of a
one-column Parquet file. The schema must have one flat, required or optional
INT32 DATE leaf. The reader checks the immutable snapshot once and reads the
raw annotation for schema ordinal one from its exact footer span. The selected
group's single column path must match the annotated leaf. The existing flat
INT32 scanner supplies the checked nullable cells. [Parquet 2.14.0 IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)
· [Parquet DATE semantics](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)

| SchemaElement annotations | Result |
| --- | --- |
| Field 10 has the sole LogicalType member 6 with an empty DateType payload, and field 6 is absent | `.logical` |
| Same modern DATE and field 6 has ConvertedType code 6 | `.logicalAndConverted` |
| Field 10 is absent and field 6 has ConvertedType code 6 | `.converted` |

Conflicting annotations, duplicate fields, malformed modern metadata,
unannotated INT32, and a wrong physical type fail with typed errors. A present
invalid modern field precludes the converted-only fallback. PyArrow reads the
conflicting fixture as DATE using its modern tag. This checked profile rejects
the disagreement.

The physical profile is the current flat, uncompressed PLAIN scanner with
Data Page V1 or V2. Scanner errors retain their causes, including
`.crcUnsupported`. `date32Slots` exposes the same signed INT32 epoch days in
Arrow's Date32 representation. `civilSlots` derives the nullable proleptic
Gregorian dates using astronomical year numbering. IPC serialization and
other Parquet scan profiles are outside this reader. [Existing scalar adapters](arrow-parquet-date.md)

## Proof contracts

`classify_ok_iff`, `checkLogicalDate_ok_iff`, and `readAnnotation_ok_iff`
characterize the accepted raw annotation and its three outcomes.
`bind_ok_iff`, `checkColumn_ok_iff`, and `readGroup_ok_iff` connect the
annotation, group path, and exact ordered scanner vector from the same
snapshot. `readGroup_date32Count` recovers the advertised count.
`RowGroup.civilSlot` preserves index and null meaning, and
`RowGroup.date32_civil` recovers the signed payload vector from its civil
view. `readGroup_scan_error` preserves the physical scanner's typed error.
[Public theorem headers](../../Silmaril/Formats/Parquet/Date/Thms.lean)

## Pinned fixtures

CPython 3.13.5 and PyArrow 26.0.1 produce the nullable V1 and required V2
files with both DATE tags, an indexed two-group file, a plain INT32 control,
and a CRC-bearing DATE. Apache Thrift 0.25.0 independently observes the
serialized field IDs and produces footer-only edits for modern-only DATE,
legacy-only DATE, a converted-code conflict, duplicate logical union arms,
a nonempty DATE payload, a mismatched column path, and DATE attached to an
INT64 leaf. The manifest identifies the Thrift edits individually. It pins
full file hashes and the host Arrow observations where applicable.

The V1 fixture includes both signed Int32 bounds, astronomical year zero,
1969-12-31, null, the epoch, and 2000-02-29. PyArrow checks ordered raw words
at the extreme dates and uses Python civil dates where representable. Lean
checks both the Date32 words and the Gregorian fields. [Fixture manifest](../../scripts/parquet-date-oracle/fixtures.json)
· [Oracle](../../scripts/parquet-date-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Thms +Silmaril.Formats.Parquet.Date.Tests parquet-flat-scan-regression'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/parquet-date-oracle/check.py
```

Use `--pyarrow-path` and `--thrift-path` for separately unpacked pinned
wheels. The fixture manifest records the wheel hashes.
