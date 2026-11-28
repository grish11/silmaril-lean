# Opt-in Parquet V1 legacy BIT_PACKED INT32 pages

`LegacyBitPackedV1.decodeInt32 physical schema codec header limits body`
reads one CRC-free, UNCOMPRESSED Data Page V1 from an optional flat
INT32 column. The caller supplies the original parsed header, the
matching column physical type and codec, the checked flat schema
levels, and the exact on-disk body from the same immutable snapshot.
The callback checks maximum levels `(0, 1)` and the original
value, definition and repetition encoding tags `0 / 4 / 3`. The
zero-width repetition section occupies no bytes. Unsupported page kinds,
schema levels, compression, and CRC presence fail admission.
[Parquet 2.14.0 level encoding][spec] · [V1 header fields][idl]

## Exact body and slot contract

The adapter applies `ScalarPage.validateFor 0` to the original V1
parameters before inspecting the payload. The shared validation checks
signed page sizes, caller size and slot caps, and exact stored extent.
The UNCOMPRESSED `Payload.decode` check also requires the advertised
expanded size to match the same bytes. The standalone MSB-first
`BitPackedLevels.readPrefix` checks its definition byte cap and
returns the exact suffix from the count-delimited definition prefix.
No length word precedes this tag-4 section.

Level 1 contributes a present value and level 0 contributes a null.
`Plain.decodeInt32` reads exactly one four-byte little-endian word for
every present level, using the untouched suffix. It rejects insufficient
and trailing bytes. `FlatPage.reconstruct` restores nullable slots in
page order. The returned `nullCount` comes from the checked V1 mask.
The tag-4 reader's policy of ignoring unused low bits in the last byte
carries over to this adapter. This is an opt-in page callback. Default,
delta, CRC, and DATE scan profiles retain their current admission rules.
[Checked tag-4 reader][levels] · [PLAIN INT32 words][plain] · [Dispatch coordination][coordination]

## Public Lean laws

- `admit_sound` binds all three original encoding fields, the V1
  kind, the physical type, the optional flat schema, codec, and absence
  of a CRC.
- `prepare_sound` proves both body sizes and caps, the slot and
  definition byte caps, the count-derived MSB-first definition prefix,
  and the exact decomposition into that prefix and the value suffix.
- `decode_ok_iff` ties the output validity to the checked mask and
  recovers the present values in order by filtering absent slots.
- `decode_wire_sound` identifies the entire value suffix with the
  consecutive four-byte words in wire order. Their count is the number
  of level ones. The null count equals the number of level zeros.
- `decode_counts` proves one slot per V1 header value. The returned
  null count equals the number of absent output slots and the header
  count minus the number of present values.

## Independent full-page fixture

The committed `optional-int32-v1.parquet` is the unmodified output
of parquet-java **1.16.0**, commit
`402c3810c372d29603e181771acebfecc71bef61`. The Java producer driver uses
`ByteBitPackingValuesWriter` in big-endian mode, `PlainValuesWriter`,
and the public `ParquetFileWriter.writeDataPage` V1 path. It explicitly
selects the legacy tag for the definition section. The whole file
reproduces byte-for-byte, including the one-page column and footer.
Its SHA-256 is
`ae79239661f40a024f706a9fb81e1494014fa41ad17ee4942b9629be33657c73`.
[Fixture][fixture] · [Producer driver][writer-driver] · [Pinned writer API][writer]

The pinned Java full-file reader recovers nine slots in order,
`[17, null, -9, 300, null, null, 0, null, -2147483648]`.
Apache Thrift **0.25.0** independently confirms the actual V1
header `[4, 21)` and body `[21, 43)`. The body splits into two
definition bytes `b280` and exactly 20 bytes for five PLAIN words.
The Lean examples open the real footer and page with the existing
framing APIs and check the returned levels, exact suffix, slots and
four nulls. They also check empty and all-null pages, size and level
budget failures, other profiles, insufficient data, and trailing values.
[Java readback][java-readback] · [Thrift verifier][oracle] · [Page provenance][provenance] · [Lean examples][examples]

**Interoperability limit.** PyArrow **26.0.1** at Arrow commit
`9e5d6978e9acf372cc989aaaf94e863fe8582c90` observed
`[null, 17, null, null, -9, 300, null, 0, null]` on this file.
The independent check shows that this pattern matches LSB-first
reading of these particular level bytes. The adapter always selects
the specification's MSB-first bit order for raw definition tag 4.
The Java result and direct MSB-first check are the value oracle.
[Specification bit order][spec] · [Pinned Arrow path][arrow]

## Reproduce

Use Java 21 and the Maven jars in the hash manifest. Use the pinned
Python and Thrift environment from the flat page fixture recipe.
Maven groups are `org.apache.parquet`, `org.apache.hadoop` for
`hadoop-client-api`, `org.locationtech.jts` for `jts-core`, and
`org.slf4j`. Set `jars` to the absolute directory holding those jars.
Run from the repository root. [Jar hashes][jars] · [Python artifact pins][recipe]

```sh
set -euo pipefail
oracle="$PWD/scripts/parquet-legacy-bit-packed-v1"
data="$PWD/data/parquet-legacy-bit-packed-v1"
replay=$(mktemp --suffix=.parquet)
trap 'rm "$replay"' EXIT
(cd "$jars" && sha256sum -c "$oracle/JAR-SHA256SUMS")
java -cp "$jars/*" "$oracle/LegacyBitPackedV1Writer.java" "$replay"
cmp "$data/optional-int32-v1.parquet" "$replay"
java -cp "$jars/*" "$oracle/VerifyFullFile.java" "$replay" |
  diff -u "$oracle/java-readback.txt" -
python3 "$oracle/VerifyFullPage.py" "$replay" |
  diff -u "$oracle/page-provenance.tsv" -
lake build --wfail +Silmaril.Formats.Parquet.LegacyBitPackedV1.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.LegacyBitPackedV1.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#L172-L198
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L698-L718
[levels]: parquet-bit-packed-levels.md
[plain]: parquet-plain.md
[coordination]: https://github.com/hiloopai/silmaril-lean/pull/4659#issuecomment-7197750977
[fixture]: ../../data/parquet-legacy-bit-packed-v1/optional-int32-v1.parquet
[writer-driver]: ../../scripts/parquet-legacy-bit-packed-v1/LegacyBitPackedV1Writer.java
[writer]: https://github.com/apache/parquet-java/blob/402c3810c372d29603e181771acebfecc71bef61/parquet-hadoop/src/main/java/org/apache/parquet/hadoop/ParquetFileWriter.java#L697-L723
[java-readback]: ../../scripts/parquet-legacy-bit-packed-v1/java-readback.txt
[oracle]: ../../scripts/parquet-legacy-bit-packed-v1/VerifyFullPage.py
[provenance]: ../../scripts/parquet-legacy-bit-packed-v1/page-provenance.tsv
[examples]: ../../Silmaril/Formats/Parquet/LegacyBitPackedV1/Examples.lean
[arrow]: https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/parquet/column_reader.cc#L150-L166
[jars]: ../../scripts/parquet-legacy-bit-packed-v1/JAR-SHA256SUMS
[recipe]: parquet-flat-page.md#independent-page-fixtures
