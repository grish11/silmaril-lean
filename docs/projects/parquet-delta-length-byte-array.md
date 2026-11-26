# Bounded Parquet DELTA_LENGTH_BYTE_ARRAY

`Silmaril.Formats.Parquet.DeltaLengthByteArray.Defs` decodes one exact
DELTA_LENGTH_BYTE_ARRAY scalar slice. Call `decode limits expected source`
with the number of present BYTE_ARRAY values. It returns `List Bytes` in wire
order. Use `Silmaril.Formats.Parquet.DeltaLengthByteArray.Thms` for the
public contracts.

The wire specification is Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `Encodings.md` SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[DELTA_LENGTH_BYTE_ARRAY wire rules][spec] · [parquet-java implementation][java]

## Wire profile and limits

- One DELTA_BINARY_PACKED INT32 length stream precedes the concatenation
  of the byte values. The delta reader verifies the declared count and
  exact extent of each block and active miniblock, stopping after the
  logical length count. The reused [delta profile][delta] defines
  canonical varints, block geometry, padding, and wraparound.
- A reconstructed length must be nonnegative before conversion to `Nat`.
  Every declared extent must exist. The concatenated payload must end with
  the last value. A zero length produces an empty byte string without
  consuming payload. Zero values use the complete delta header and an
  empty payload. Null slots are represented outside the scalar slice.
- `limits.lengths.bytes` caps the full source. The other delta limits
  cap the count and block geometry and work. `limits.payloadBytes` caps
  the whole suffix and `limits.valueBytes` caps each reconstructed value.
  Payload lengths and extents use `Nat`. The API preserves opaque bytes
  including embedded zero octets and invalid UTF-8.

`DeltaBinaryPacked.parsePrefix` exposes the reusable split as
`(Stream × List UInt8)`. The first result retains the length wire AST and
the second is the untouched suffix. `parsePrefix_sound` proves
`source.toList = stream.wire ++ suffix`. `parsePrefix_consumed` identifies
both the prefix and suffix by the exact offset `stream.wire.length`.
`DeltaBinaryPacked.parse` accepts exactly when that suffix is empty, as
stated by `parse_ok_iff`.

`assemble_ok_iff` characterizes success over an already decoded length
list. The signed lengths agree pointwise with the value sizes, the input is
their concatenation, and both byte caps hold. `decode_sound` proves that
contract for the parsed lengths and gives the whole input extent as the
length prefix plus the sum of value sizes. It also proves the output count.

## Page dispatch seam

For a checked BYTE_ARRAY column and data-page encoding `6`, a client can use
`ScalarPage.prepareFor 6` with its existing parameters and exact body. Pass
`page.scalars` and `page.mask.count true` to this decoder. Use
`FlatPage.reconstruct page.mask values` to place the results in nullable
slots. The adapter takes the decompressed scalar slice. Frame traversal,
level decoding, page dispatch, row-group assembly, logical annotations, and
DELTA_BYTE_ARRAY stay outside this codec.

## Independent fixtures

The [manifest][vectors] is produced by the [Java oracle][oracle], using
parquet-java **1.16.0** at commit `402c3810c372d29603e181771acebfecc71bef61`.
Its delta reader independently extracts every length and the byte offset
of the concatenated payload. The DELTA_LENGTH_BYTE_ARRAY reader checks the
individual opaque values against the source vectors. The [Lean examples][lean]
check the same bytes, lengths, and split offsets. The five cases include
zero values, one empty value, mixed empty and non-ASCII bytes, a 130-byte
value, and a multi-block length stream. Additional cases cover negative
lengths, truncation, trailing data, count mismatch, and each byte cap.

The TSV columns are case name, value count, length-prefix byte count, and
hexadecimal scalar bytes. Its SHA-256 is
`d06fd632a662cccabacf7e15dc286664606c9a9b9bb9ada25772fb68476b3ee7`.

Use JDK 17 or later and the pinned jars from the [PLAIN fixture recipe][plain].
With `jars` set to that directory, run from the repository root.

```sh
set -o pipefail
java -cp "$jars/*" scripts/parquet-delta-length-byte-array/DeltaLengthOracle.java |
  diff -u tests/formats/parquet-delta-length-byte-array/parquet-java-1.16.0.tsv -
lake build --wfail +Silmaril.Formats.Parquet.DeltaBinaryPacked.Examples \
  +Silmaril.Formats.Parquet.DeltaLengthByteArray.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.DeltaBinaryPacked.Examples +Silmaril.Formats.Parquet.DeltaLengthByteArray.Examples'
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#delta-length-byte-array-delta_length_byte_array--6
[java]: https://github.com/apache/parquet-java/tree/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/column/values/deltalengthbytearray
[delta]: parquet-delta-binary-packed.md
[plain]: parquet-plain.md#independent-fixtures
[vectors]: ../../tests/formats/parquet-delta-length-byte-array/parquet-java-1.16.0.tsv
[oracle]: ../../scripts/parquet-delta-length-byte-array/DeltaLengthOracle.java
[lean]: ../../Silmaril/Formats/Parquet/DeltaLengthByteArray/Examples.lean
