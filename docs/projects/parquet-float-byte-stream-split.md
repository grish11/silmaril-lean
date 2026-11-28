# Checked Parquet FLOAT BYTE_STREAM_SPLIT row groups

`Silmaril.Formats.Parquet.FloatByteStreamSplit.readGroup limits source name ordinal`
returns `List (Option UInt32)` for one selected group of a plaintext Parquet
file with one named optional flat FLOAT leaf. The ordinal is zero-based.
`some` carries the raw IEEE 754 word, including its sign and any NaN
payload. `none` represents a null slot.

The reader checks the immutable snapshot and matches the named leaf and
the selected group's sole local column by path, physical type, and slot
count before using the chunk offsets. The column must declare codec 0 and
advertise BYTE_STREAM_SPLIT (9), with RLE (3) permitted for its levels.
The reader admits V1 with RLE level tags and V2 with flat level extents.
It rejects CRC-bearing pages, dictionary and index pages, other scalar
encoding tags, and legacy BIT_PACKED levels.

The file and footer parsers have byte and structural limits. The group
row cap and compressed chunk cap apply before framing. The bounded
framer records the original page order and spans. Before slicing any
body, the reader checks both declared page sizes, the page slot limits,
and the sum of declared slots against the selected group's row count.
Each original body goes to `ByteStreamSplitPage.decode` with the header's
original sizes, encoding, counts, and V1/V2 level parameters. That decoder
checks the exact split-byte extent before transposing the lanes. The reader
concatenates the nullable slots in frame order and checks the final count.
Errors on admitted frames carry the original group index, page index
within the chunk, and absolute header offset.
[Page preparation and lane decoder](parquet-byte-stream-split-page.md)

## Theorem

`FloatByteStreamSplit.readGroup_wire` witnesses the checked snapshot, exact
group lookup, named optional leaf, and matched column chunk. It gives the
original `Page.readChunk` equation and pairs frames with their output lists
using `List.Forall₂`. Each `PageWire` witness gives the exact version-specific
body layout, the recovery of the definition mask from the nullable slots,
and the four-lane byte order for all present words. Those words are
interpreted by `Plain.readUInt32Word`. Concatenating the per-page lists
gives the returned bits and exactly `group.numRows.toNat` slots.
[Theorem header][thms] · [Frame contracts][page-thms]

## Pinned fixture evidence

The wire specification is Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. PyArrow **26.0.1**, Arrow
commit `9e5d6978e9acf372cc989aaaf94e863fe8582c90`, writes both files.
Apache Thrift **v0.25.0**, commit `27e8a425ffb498e190df3a12e239326bf5ba9ed6`,
independently reads footer codecs, page headers and extents. The oracle
checks the lanes against independently transposed input words and compares
readback validity and raw UInt32 buffers. Each file has three groups of
eight nullable slots, with two pages per group and an all-null final page.
The inputs include both zero signs, quiet NaNs with different signs and
payloads, infinities, and subnormals.
[Encoding specification][spec] · [Pinned producer packages][pins]

| Fixture | SHA-256 |
| --- | --- |
| `float-bss-v1.parquet` | `19138d5018044414ad5837ac9ffa111302255213c189df0e047d83aed6d1adfd` |
| `float-bss-v2.parquet` | `d619155d5d36f6e402816c598d5744ebd8f0b576234e1f81f705c1da3106d5f3` |

The V2 controls change the actual page encoding or the footer codec,
and alter the first page's definition mask together with its declared
null count to induce short and surplus value lanes. Another mutation
makes the page slot total seven in an eight-row group. That control
includes a short first page and checks that the group total fails before
body decoding. Additional controls exercise selected name, group index,
and file, row, framing, page size, and page count budgets.
[Regression checks][tests] · [Independent oracle][oracle]

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-float-byte-stream-split/Oracle.py "$fixture_tmp"
diff -r data/parquet-float-byte-stream-split "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.FloatByteStreamSplit.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.FloatByteStreamSplit.Tests +Silmaril.Formats.Parquet.ByteStreamSplitPage.Examples parquet-page-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-float-byte-stream-split/Axioms.lean
```

[thms]: ../../Silmaril/Formats/Parquet/FloatByteStreamSplit/Thms.lean
[page-thms]: ../../Silmaril/Formats/Parquet/Page/Thms.lean
[tests]: ../../Silmaril/Formats/Parquet/FloatByteStreamSplit/Tests.lean
[oracle]: ../../scripts/parquet-float-byte-stream-split/Oracle.py
[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#byte-stream-split-byte_stream_split--9
[pins]: parquet-flat-page.md#independent-page-fixtures
