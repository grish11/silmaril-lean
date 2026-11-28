# Selected PLAIN BYTE_ARRAY files

`Silmaril.Formats.Parquet.Plain.ByteArray.File.openFile limits bytes name layout`
binds one named physical BYTE_ARRAY leaf of a checked plaintext Parquet
snapshot. The caller selects `.required` or `.optional`. Every leaf is a
direct required or optional child of the root. Other flat physical siblings
are allowed. The selected chunk must match the bound leaf, its column ordinal,
and the group row count. Present values are opaque `Bytes`. An empty byte
string is distinct from a null. Logical annotations and UTF-8 interpretation
are outside this profile. [Public entry points][defs] · [FlatColumn](parquet-flat-column.md)

`Checked.readGroup limits index` returns `List (Option Bytes)` for a zero-based
footer group ordinal. `File.readAll` returns a one-field event stream with
layout in the field kind. It emits one complete batch per successful group in
footer order and stops at the first failure, retaining preceding batches.
Indexed reads return the original `FlatColumn.Error File.PageError`.
The event stream carries that same payload inside `File.Error.column`.
Page admission and decoder errors include the original group, column,
page and header offset. Chunk framing errors carry group and column context
with the original `Page.Error`.

## Admission and bounds

Each selected chunk requires codec 0 and actual PLAIN value tag 0 on every
page. Both Data Page V1 with RLE level tags and Data Page V2 with flat, raw
level sections are admitted. The binder accepts footer encodings PLAIN and
RLE for levels and checks actual page encodings separately. It rejects CRC,
dictionary and non-data frames, legacy BIT_PACKED levels, external chunks
and unsupported page offsets. It reads the complete declared selected
chunk. Compressed codecs and index-driven reads are separate profiles.

Opening checks the file byte cap before parsing and the file's advertised
total row count after footer validation. The column caps bound chunk bytes,
page-header lookahead, page count, both declared page sizes and row
materialization. All page framing, admission and declared group slot counts
precede body extraction. The scalar decoder uses the same page and slot caps.
The BYTE_ARRAY decoder checks the entire scalar extent and each four-byte
length before allocating that value's bytes. [Page contracts](parquet-scalar-page.md) ·
[PLAIN value wire contract](parquet-plain-byte-array.md)

## Lean laws

- `File.openFile_wire` identifies the checked snapshot of the original
  input, the file bounds and the exact serialized leaf with its name,
  physical type and layout.
- `File.readGroup_wire` identifies the original indexed group, chunk and
  `Page.readChunk` result. For each frame in order it relates the full
  on-disk body to the checked definition mask and exact PLAIN length-and-byte
  sequence. The output is the concatenated nullable slots with the
  advertised count.
- `File.readAll_order` equates the event trace with the shared
  `Reader.denoteGroups` over the checked group's ordinal range. A group
  contributes a batch after a complete read. A failure determines the
  terminal cause and leaves the preceding batches in order.

[Theorem header][thms]

## Independent fixtures

Parquet Format **2.14.0** is pinned at
`04d56f291ff963e98bc37ab8100e2fc133ff583c`.
The `parquet.thrift` SHA-256 is
`d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
PyArrow **26.0.1** is from Arrow at `9e5d6978e9acf372cc989aaaf94e863fe8582c90`.
The independent Compact page oracle uses Thrift **v0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`.
[Standards and producer provenance](arrow-parquet-coverage.md) ·
[Package pins](parquet-flat-page.md#independent-page-fixtures) · [Oracle][oracle]

Each clean file contains three groups of 12 rows. The leading INT32
sibling precedes an optional BYTE_ARRAY leaf with page counts `[4, 8]`
and a required BYTE_ARRAY leaf with page counts `[4, 4, 4]`. Both
readers check exact group and slot order, empty values and opaque octets
including invalid UTF-8. Thrift and the producer oracle check the actual
tags and full on-disk extents, including the exact PLAIN suffix.

| Fixture | SHA-256 |
| --- | --- |
| `plain-byte-array-v1.parquet` | `1e5bfe8a5e580a0368300b3d7809b2c4396ab814eb57b006775b4f849906fc29` |
| `plain-byte-array-v1-bad-length.parquet` | `474b8c262eb7275e018cc8dd7bd7d0ea0fdb5af2b3a2833e5ec58a4babdb140e` |
| `plain-byte-array-v2.parquet` | `f9fe23f0a5b2a839d9a97b717f8e47062e88d6a7d33139a4129cfbbbd213d354` |
| `plain-byte-array-v2-bad-length.parquet` | `bf016635dee7a6d6289360f6c31f0fe92ee9682e75deb41f18eba3bc4168bf04` |

In each damaged file a value length in group 1, column 1, page 1 grows
from 2 to 65,535 at byte 633 (V1) or 672 (V2). PyArrow rejects that group
for the selected leaf. Lean emits the preceding 12 rows and preserves
`ScalarPage.Error.plain .truncated` at header byte 608 (V1) or 646 (V2).
Both still read group 2 by direct index and read the required sibling
through EOS. Additional guards check the exact PLAIN page tag, selected
field, file caps and per-value byte cap. [Regressions][tests]

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-plain-byte-array-file/Oracle.py "$fixture_tmp"
diff -r data/parquet-plain-byte-array-file "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.File.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Plain.ByteArray.File.Tests +Silmaril.Formats.Parquet.Plain.ByteArray.Examples +Silmaril.Formats.Parquet.ScalarPage.Examples +Silmaril.Formats.Parquet.MixedBooleanFloat.Tests parquet-footer-regression parquet-page-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-plain-byte-array-file/Axioms.lean
```

[defs]: ../../Silmaril/Formats/Parquet/Plain/ByteArray/File/Defs.lean
[thms]: ../../Silmaril/Formats/Parquet/Plain/ByteArray/File/Thms.lean
[tests]: ../../Silmaril/Formats/Parquet/Plain/ByteArray/File/Tests.lean
[oracle]: ../../scripts/parquet-plain-byte-array-file/Oracle.py
