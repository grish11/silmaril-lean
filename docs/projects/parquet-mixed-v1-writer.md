# Checked mixed INT32 and BYTE_ARRAY Parquet writer

`Silmaril.Formats.Parquet.MixedV1Writer.emit limits input` emits one
complete flat Parquet file with exactly one row group. The group has one
INT32 column followed by one opaque BYTE_ARRAY column. Each column has
one uncompressed PLAIN V1 data page and an explicit required or optional
layout. The names must be distinct and nonempty, and both slot lists
must have the same length. Nulls, present empty values, and embedded
zero or non-UTF-8 octets keep their original row positions.

The writer uses the existing [INT32 page][int-page] and [BYTE_ARRAY
page][byte-page] writers. Its bounded Compact footer reuses the INT32
file writer's field, list and typed chunk serializers. It records the
columns in input order, with the INT32 page starting at byte 4, the
BYTE_ARRAY page adjacent to it, and the footer immediately after both
pages. Footer recovery compares the complete metadata. The chunk checks
recover each exact absolute interval, its single page header and the
original body slice. The existing mixed reader then reopens the file and
checks the ordered pairs before emission succeeds.

The caller supplies an aggregate file budget, a footer parser and
serialization budget, separate page limits and separate mixed-reader
limits. The writer bounds page footprints before assembling them and
allows the footer only the remaining space after the trailer. The
reader may impose stricter file, footer, row, page or value caps. Its
original cause remains inside the tagged readback error.

`emit_checked` exposes the exact footer and page checks and readback.
`rows_exact` proves that the pairing consumes all slots from both
columns. `emit_wire` relates the successful rows to the original
checked wire chunks at footer ordinal zero. [Theorems][laws]

A zero-row group is supported with two real, nonzero-offset page
headers. The optional page has the four-octet zero definition length.
This profile uses unannotated leaves, with no statistics, CRC,
dictionary, compression, or other page versions. It emits one group.

The [oracle][oracle] pins five genuine Lean files. Apache Thrift
0.25.0 checks exact footer fields, page headers, absolute offsets and
body bytes. PyArrow 26.0.1 checks both fields in physical order and all
nullable slots, including all four required/optional schema combinations
and a zero-row group. Lean also checks exact file-cap admission and
eight typed refusal controls.

```sh
lake build --wfail +Silmaril.Formats.Parquet.MixedV1Writer.Checks
python3.13 scripts/parquet-mixed-v1-writer-oracle/check.py --out /tmp/parquet-mixed-v1-writer
```

[int-page]: parquet-plain-v1-writer.md
[byte-page]: parquet-plain-byte-array-v1-writer.md
[laws]: ../../Silmaril/Formats/Parquet/MixedV1Writer/Thms.lean
[oracle]: ../../scripts/parquet-mixed-v1-writer-oracle/check.py
