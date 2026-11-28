# Opt-in PyArrow page-less DATE groups

Parquet 2.14.0 describes a column chunk as containing one or more pages.
Its IDL requires `ColumnMetaData.data_page_offset` to locate the first data
page. It defines no zero sentinel for that field. The separate deprecated
`ColumnChunk.file_offset` can be zero when the writer does not store a
second copy of the column metadata. PyArrow 26.0.1 emits explicit zero-row
groups with no pages and writes zero for both offsets. The new API treats
this as a producer convention. Strict DATE and generic footer admission
continue to require their original page intervals.
[Parquet file layout](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#file-format)
· [Pinned Parquet IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L907)

`Date.PageLess.readAll` and `Date.PageLess.toIpc` opt in to a one-column
plaintext INT32 DATE profile with the pinned PyArrow creator string and
metadata version 2. A page-less group has one chunk, zero rows, zero
values, zero compressed and uncompressed sizes, and zero row-group file
offset, column-chunk file offset, and data-page offset. Its chunk has
codec UNCOMPRESSED, an encoding list containing only RLE, and an explicit
empty page-encoding-statistics list. Its raw fields exclude alternate
locations, indexes, dictionaries and Bloom filters. The exact leaf path
and original DATE annotation are checked. A provided raw ordinal must
agree with its original footer position.

All framed groups pass the existing strict footer validator and DATE
page scanner, with the original offsets, exact source bytes and default
CRC policy. Framed chunks must be contiguous from the leading magic to
the footer in original order, with matching group extent metadata and no
auxiliary data ranges. A page-less group occupies no interval. The snapshot
retains the original metadata and dense group indices. The profile avoids
interpreting offset zero as a readable page, synthesizing bytes, or
discarding a declared group.
[Footer profile](../../Silmaril/Formats/Parquet/Footer/PageLessInt32/Defs.lean)
· [DATE entry points](../../Silmaril/Formats/Parquet/Date/PageLess/Defs.lean)

`checkPageLessInt32_exact` binds the observed metadata and every group
ordinal to the input. `readGroup_pageLess` gives the exact zero-row
result after the field-path and flat-schema checks. `readAll_noGroups`
and `readAll_oneEmpty` distinguish the schema-only trace and an explicit
empty batch. `readAll_eof` and `toIpc_readback` retain the same descriptor
and one ordered batch per original group on success. A nonempty group
before or after a page-less group is read by the regular decoder.
[Theorem header](../../Silmaril/Formats/Parquet/Date/PageLess/Thms.lean)

## Independent checks

PyArrow 26.0.1 produces an optional DATE file with batch row counts
`[2, 0, 2]`, a required one-empty-group file and a required schema-only
file. Apache Thrift 0.25.0 reads the original Compact metadata independently.
PyArrow checks the exact signed nullable slots, descriptor and explicit
batch count in the Lean-emitted IPC. The original strict reader still
refuses the two explicit zero-page files. Seven independent Thrift edits
exercise value count, data offset and extent, dictionary offset, nonempty
page statistics, incorrect ordinal and overlapping framed chunks.
[Fixture hashes and raw metadata](../../scripts/parquet-date-pageless-oracle/fixtures.json)
· [Oracle](../../scripts/parquet-date-pageless-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.PageLess.Thms +Silmaril.Formats.Parquet.Date.PageLess.Tests +Silmaril.Formats.Parquet.Footer.PageLessInt32.Thms'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-pageless/Axioms.lean
python3 -I scripts/parquet-date-pageless-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
