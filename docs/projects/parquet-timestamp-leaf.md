# Selected Parquet TIMESTAMP leaves and row groups

`Parquet.Timestamp.Leaf.openLeaf` checks one immutable plaintext snapshot
and binds a flat INT64 TIMESTAMP leaf by its serialized schema ordinal. The
schema includes the root at ordinal zero. The selected leaf's ordinal,
physical type, repetition and name agree in the checked schema and the
annotation reader's exact footer slice. The binding retains the snapshot and
the effective levels for a required or optional leaf.
[Parquet 2.14.0 Thrift IDL] · [Standalone TIMESTAMP annotation]

`readGroup` takes the retained binding and a zero-based row-group index.
For the flat schema, chunk ordinal is leaf ordinal minus one. The chunk's
singleton path, physical type, and value count must match the bound leaf and
the selected group. The reader checks its declared data interval before the
footer and rejects an overlap with another declared chunk. It frames that
interval in order, checks the declared slot total against the group count
and row budget, and passes each original header and exact payload slice to
`Timestamp.Page.decode`. The compressed byte budget also applies before the
payload slice is copied.

The physical profile covers uncompressed PLAIN Data Page V1 and V2 with
required or optional flat levels. It returns ordered nullable signed ticks.
CRC-bearing pages, dictionary and index pages, unsupported encodings and
compression receive typed errors. Errors from the original page decoder
include the zero-based page index.
[Standalone TIMESTAMP pages]

## Annotation compatibility

| Selected leaf annotation | Checked interpretation |
| --- | --- |
| Modern TIMESTAMP | Accept MILLIS, MICROS, and NANOS. The modern `isAdjustedToUTC` flag selects UTC instants or local readings. |
| Modern TIMESTAMP plus a matching legacy tag | Accept `TIMESTAMP_MILLIS` with MILLIS or `TIMESTAMP_MICROS` with MICROS. The modern flag still controls interpretation. |
| Conflicting legacy tag or a legacy tag on modern NANOS | Reject with the existing converted-type error. |
| Legacy-only timestamp or unannotated INT64 | Reject with missing modern field 10. |
| Physical INT96 or nested or repeated selected leaf | Reject in this profile. |

Parquet's flag and unit determine the result type. No timezone annotation or
UTC offset is inferred from the count. The reader exposes a selected column
on one checked byte source. DATE, the generic scanner, IPC, and CSV use their
existing interfaces. [TIMESTAMP semantics]

## Public contracts

- `openLeaf_sound` identifies the original checked source.
- `bind_sound` identifies the selected checked schema entry, original footer
  annotation and matched levels.
- `selectChunk_sound` identifies the actual group, column ordinal and path,
  INT64 type, codec, declared row count and disjoint data interval.
- `readGroup_sound` relates the output to the contiguous chain of original
  frames and the original nullable physical slots. The descriptor is mapped
  pointwise in wire order, and the slot count equals the advertised group
  row count.

## Fixtures and checks

Pinned PyArrow 26.0.1 files contain distinct neighboring leaves, multiple
pages per chunk, two row groups, all three units in both interpretations,
mixed nulls, a required leaf, negative values, and both Int64 endpoints.
PyArrow independently reads each selected group's exact signed words. Thrift
0.25.0 checks page boundaries and mutates real producer files to exercise
matched and conflicting legacy tags, a legacy-only tag, invalid path,
aliased chunks, inconsistent counts, a truncated payload, and an unsupported
page encoding. Separate producer files exercise CRC, dictionary and
compression rejection. The length-framed file bytes are pinned by SHA-256.
[Pinned Python wheel requirements]

```sh
lake build --wfail Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.Thms +Silmaril.Formats.Parquet.Date.Thms parquet-flat-scan-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-timestamp-leaf/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-leaf
/tmp/parquet-timestamp-leaf/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-leaf/bin/python -I tests/formats/parquet-timestamp-leaf/check-fixtures.py
```

[Parquet 2.14.0 Thrift IDL]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[TIMESTAMP semantics]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#timestamp
[Standalone TIMESTAMP annotation]: parquet-timestamp-annotation.md
[Standalone TIMESTAMP pages]: parquet-timestamp-page.md
[Pinned Python wheel requirements]: ../../tests/formats/columnar-timestamp-wire/requirements.txt
