# Bounded Parquet BYTE_STREAM_SPLIT

`Silmaril.Formats.Parquet.ByteStreamSplit.Defs` decodes one exact scalar
slice for encoding `9`. Call `decode kind limits count source` with the
physical kind and present-value count. `decodeWords` exposes the same
checked transposition as a list of raw byte words. The public proof header
is `Silmaril.Formats.Parquet.ByteStreamSplit.Thms`.

The wire specification is Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `Encodings.md` SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[BYTE_STREAM_SPLIT wire rules][spec] · [parquet-java implementation][java]

## Wire profile

A slice with `N` values of `K` bytes contains `K` consecutive lanes of `N`
bytes. Lane `j` contributes original byte `j` to every word in value order.
The byte at lane `j`, row `i`, comes from offset `j * N + i` within the slice.
Exactly `K * N` bytes are required. There is no padding, count field, or
width field. For zero values, the scalar slice is empty.

| Physical kind | Width | Decoded value |
| --- | --- | --- |
| INT32 | 4 | `Int32` |
| INT64 | 8 | `Int64` |
| FLOAT | 4 | `UInt32` raw IEEE 754 bits |
| DOUBLE | 8 | `UInt64` raw IEEE 754 bits |
| FIXED_LEN_BYTE_ARRAY | Configured schema width | Opaque `Bytes` in original byte order |

The decoder applies the [PLAIN word interpretation][plain] to the
reassembled word. FLOAT and DOUBLE preserve every bit, including NaN
payloads and signs, signed zeros, infinities, and subnormals.

Before allocating output, the reader checks the caller's width, count,
and byte caps and the exact extent with `Nat` arithmetic. The checked
profile requires a positive width and width and count below `2^31`.
A fixed width must come from the caller's checked schema. Bad widths are
rejected even for an empty slice. Short and trailing input bytes are
reported separately. The reader uses checked positions on the original
`Bytes` array for each byte of each output word.

The API takes the decompressed scalar slice, with any definition levels
already handled by the caller. Page framing, compression, scan dispatch,
logical types, and a writer are outside this module.

## Public proofs

- `decodeWords_ok_iff` characterizes success by the width, count, byte
  bounds, and exact extent, together with the indexed `LaneOrder` relation.
  It proves the number and width of the words and the source byte at
  every in-range lane and row.
- `decode_sound` proves that the typed result applies `Kind.readWord`
  to those exact words in order and has the requested count.

## Independent fixtures

The [manifest][vectors] records seven uncompressed, non-dictionary Data
Page V1 bodies produced by PyArrow **26.0.1** at Arrow commit
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`. The [PyArrow oracle][python]
checks the exact body extent and encoding ID through Apache Thrift
**v0.25.0**, compares with an independent byte-stride calculation, and
reads back the original raw value buffer. Fixtures use a required
single-column schema so no definition bytes precede the scalar lanes.

The [Java oracle][oracle-java] uses parquet-java **1.16.0**, commit
`402c3810c372d29603e181771acebfecc71bef61`. Its typed readers check the
five common vectors and its writers produce the same lane bytes as the
first five PyArrow rows. The two additional PyArrow cases carry unusual
NaN payloads and subnormals. The parquet-java writer canonicalizes NaNs,
so its cross-check uses canonical NaNs. The [Lean examples][lean] verify
all seven vectors, the specification's asymmetric lane-order example, and
short, trailing, oversized, empty, and invalid width or count cases.

The TSV columns are case name, count, width, and hexadecimal lane bytes.
The SHA-256 is `63b073b2613ac7aab6895674f55e4dbcfca7dbb2717e0a118eff1c782a82c074`.
Use the pinned little-endian Linux Python and Thrift artifacts from the
[flat-page fixture recipe][flat], and JDK 17 or later with the pinned Maven
jars from the [PLAIN fixture recipe][plain]. Set `jars` to the jar directory
and put the Python packages on the import path before running from the repo root.

```sh
set -o pipefail
fixture=tests/formats/parquet-byte-stream-split/pyarrow-26.0.1.tsv
python3 scripts/parquet-byte-stream-split/PyArrowOracle.py | diff -u "$fixture" -
java -cp "$jars/*" scripts/parquet-byte-stream-split/ByteStreamSplitOracle.java |
  diff -u <(head -n 5 "$fixture") -
lake build --wfail +Silmaril.Formats.Parquet.ByteStreamSplit.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ByteStreamSplit.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#byte-stream-split-byte_stream_split--9
[java]: https://github.com/apache/parquet-java/tree/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/column/values/bytestreamsplit
[plain]: parquet-plain.md#independent-fixtures
[flat]: parquet-flat-page.md#independent-page-fixtures
[vectors]: ../../tests/formats/parquet-byte-stream-split/pyarrow-26.0.1.tsv
[python]: ../../scripts/parquet-byte-stream-split/PyArrowOracle.py
[oracle-java]: ../../scripts/parquet-byte-stream-split/ByteStreamSplitOracle.java
[lean]: ../../Silmaril/Formats/Parquet/ByteStreamSplit/Examples.lean
