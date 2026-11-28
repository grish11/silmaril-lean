# PLAIN INT32 and delta-length BYTE_ARRAY group projection

`Int32ByteArrayGroup.DeltaLength.readFileRowGroup limits bytes int32Name
byteArrayName index` reads one zero-based footer group from a plaintext
Parquet file. The profile binds a required physical INT32 leaf and an
optional physical BYTE_ARRAY leaf by their exact, distinct names on the
same checked snapshot. Other flat siblings can be present. The result is
an ordered list of nullable pairs, with signed INT32 values and opaque
BYTE_ARRAY values. Empty bytes and null slots are distinct.
[Definitions][defs] · [Same-snapshot binding](parquet-int32-byte-array-group.md)

## Admission and bounds

The selected INT32 chunk uses PLAIN (tag 0). The selected BYTE_ARRAY
chunk advertises DELTA_LENGTH_BYTE_ARRAY and every data page must use
actual tag 6. Both chunks use codec 0 and either Data Page V1 with RLE
level tags or Data Page V2 with flat levels. The inherited walk rejects
CRC, dictionary and non-data pages, external paths and unsupported
offsets in the selected read. It checks file metadata globally and page
bodies for the selected chunks of the requested group. Logical annotations
are outside the physical contract.

The opener checks the file byte cap. FlatColumn applies chunk, page and
slot limits and verifies the group's declared slot sum before slicing bodies. The delta reader receives
the original typed header and complete on-disk frame body. The length
stream inherits the page byte and slot caps and has separate bounds on
block size, miniblocks per block and block count. Each decoded value
has the selected value byte cap. [Shared column walk](parquet-flat-column.md) ·
[Delta page preparation](parquet-delta-page.md) ·
[Exact length and payload reader](parquet-delta-length-byte-array.md)

The reader completes the INT32 leg before reading the binary leg. Each
failure carries its original cause and coordinates. A selected page
failure identifies the group, column, column name, page and original
header byte. The exact same-group counts are checked before pairing.
The opt-in entry point has row-group scope and the existing PLAIN
readers keep their tag-0 policy.

## Lean contracts

- `openFile_snapshot` witnesses the original checked input and both
  original serialized leaf ordinals.
- `readBinary_wire` witnesses the original indexed chunk and ordered
  frames. Every binary frame retains the original body and checked
  definition mask. Its scalar slice is the exact delta length stream
  followed by the complete concatenated opaque payload. The signed
  lengths agree with the decoded sizes and the present count.
- `readGroup_of_columns` gives equal counts and exact pairing whenever
  both selected column reads succeed.
- `readGroup_wire` ties both decoded lists to the same footer group and
  its row count. The ordered pairing unzips to both complete selected
  lists independently of the page cuts.
- `readGroup_int32_error` and `readGroup_byteArray_error` state the first
  error precedence with its unchanged nested cause.

[Theorem header][thms]

## Independent fixtures

Parquet Format **2.14.0** is pinned at
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The `parquet.thrift` SHA-256 is
`d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
PyArrow **26.0.1** is from Arrow at `9e5d6978e9acf372cc989aaaf94e863fe8582c90`.
The independent Compact header checks use Thrift **v0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. [Standards and provenance](arrow-parquet-coverage.md) ·
[Package pins](parquet-flat-page.md#independent-page-fixtures)

Both clean files have three 12-row groups and an unselected INT64 decoy.
Within each group the INT32 page counts are `[8, 4]` and the optional
BYTE_ARRAY page counts are `[4, 4, 4]`. The middle binary page contains
four nulls. PyArrow and Lean read back all 36 ordered pairs per version,
including empty, embedded-zero and non-UTF-8 byte strings.

| Fixture | SHA-256 |
| --- | --- |
| `plain-int32-delta-length-v1.parquet` | `88dfeea1d8ab58060fc00f00efc38aa6c4ab65d0a3694961cea863f5c47318cd` |
| `plain-int32-delta-length-v2.parquet` | `64ccdd4dbc81b874c57bdbf7eab4495d76fe46a1ce2c36c1a96b445918367d53` |
| `plain-int32-delta-length-v2-bad-tag.parquet` | `8c510f67983261ae683f130b3c77207662a09e05d54d83a5c8ab89aca25b71bb` |
| `plain-int32-delta-length-v2-bad-length.parquet` | `5932a720e63c8316d0442c2fa06bfd61e201d7ce9004243cfc5158e669e02f4b` |

Both controls target group 1, column 1, page 2 at header byte 760. The tag
control changes the actual tag at byte 776 to 3 and fails during page
admission. The scalar control changes the first length at byte 792 from
2 to 3, increasing each reconstructed length by one. It preserves the
headers and earlier pages and fails with a truncated value payload after
the earlier pages decode. PyArrow rejects both selected reads and still
reads the unaffected INT32 column and the other groups. Lean preserves
the indexed causes without returning partial pairs. [Oracle][oracle] ·
[Lean regressions][tests]

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-int32-delta-length-group/Oracle.py "$fixture_tmp"
diff -r data/parquet-int32-delta-length-group "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Tests +Silmaril.Formats.Parquet.DeltaPage.Examples +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Tests +Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Tests parquet-flat-scan-regression parquet-page-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-int32-delta-length-group/Axioms.lean
```

[defs]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/DeltaLength/Defs.lean
[thms]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/DeltaLength/Thms.lean
[tests]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/DeltaLength/Tests.lean
[oracle]: ../../scripts/parquet-int32-delta-length-group/Oracle.py
