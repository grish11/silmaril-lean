# Parquet RLE/bit-packed hybrid values

`Silmaril.Formats.Parquet.Hybrid.Defs` implements an exact-slice reader for
the hybrid encoding's `encoded-data` segment. Import
`Silmaril.Formats.Parquet.Hybrid.Thms` for its contracts. The code shares
the library byte carrier and little-endian byte arithmetic.
[Arrow and Parquet coverage](arrow-parquet-coverage.md)

The wire reference is Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The SHA-256 of the raw
`Encodings.md` is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[Hybrid encoding specification][spec]

## Wire rules and reader profile

- A run starts with an unsigned base-128 header. An even code represents
  an RLE count of `code / 2`. Its repeated value takes `(width + 7) / 8`
  little-endian bytes. An odd code represents `code / 2` packed groups.
  Each group holds eight values in `width` bytes, with the first value
  occupying the least significant `width` bits.
- Both physical run lengths must be in `[1, 2^31 - 1]`. The reader accepts
  bit widths from 0 through 32, including zero-width runs whose values are
  all zero and whose payloads are empty. The run header is still required.
- The reader requires minimal ULEB spellings, a terminating byte within
  five octets, and a header in the unsigned 32-bit range. It rejects RLE
  values with bits above the requested width. These are checked profile
  decisions for malformed or redundant spellings.
- The exact count is supplied out of band. A final packed run can contain
  at most seven surplus values, whose bits the reader ignores. All bytes of
  that last group must be present. RLE runs may never overshoot the count.
  Once the expected count is reached, any remaining byte is an error.
  A zero count requires an empty slice.
- Byte and value budgets are supplied by the caller and checked before
  expansion. The expected count must fit the nonnegative signed-32-bit
  domain. Size arithmetic uses `Nat`. Run payload lengths and remaining
  counts are checked before constructing the corresponding value lists.

## Client API and proofs

- `decode width expected limits source` returns unsigned values as
  `List Nat`. A levels reader supplies the schema-derived width and checks
  values against the schema's maximum level. A dictionary-index reader
  supplies the stream's width and checks each decoded index against the
  dictionary length. Each client provides an exact slice after interpreting
  its own framing, including any four-byte encoded length or dictionary
  bit-width octet.
- `encodeRepeated width count value` writes one explicit nonempty RLE run
  with a minimal header. Callers can concatenate exact run bytes. Packed
  writing and automatic run selection are outside the writer profile.
- `readHeader_ok_iff`, `readRun_ok_iff`, and `unpackGroup_getElem`
  connect the bounded scan to exact consumed bytes and little-endian
  group bit positions. `run_values_length` gives physical cardinality.
- `decode_ok_iff` gives soundness and completeness against `Wire`
  within the budgets. `decode_length` and `decode_values_fit` give the
  exact output count and unsigned width bound. `decode_encodeRepeated`
  gives the round trip for a successful explicit RLE write under adequate
  reader budgets.

This slice covers the hybrid encoding's run stream. Page and dictionary
framing, level semantics, dictionary lookup, deprecated BIT_PACKED,
compression, and logical annotations belong to downstream readers.

## Fixtures and reproduction

[The manifest][vectors] records five raw encoded-data slices generated and
read back by parquet-java **1.16.0**, commit
`402c3810c372d29603e181771acebfecc71bef61` (Apache-2.0). They include a
multi-octet RLE header, two packed groups with final padding, a mixed run
stream, zero width, and full width. The manifest SHA-256 is
`7e11ae0c641441a0e6f482cd41f98bf8e515c2096183cad515e8b04ee262a099`.
The Lean fixtures bind those bytes to the manifest and check the RLE
writer against the same independent payloads. Additional closed cases
exercise nonzero padding, count and byte limits, zero and oversized run
lengths, nonminimal and overflowing headers, bad repeated-value bits,
truncation, and trailing data. [Oracle program][oracle] ·
[Pinned writer and reader sources][java] · [Lean fixtures][lean]

For JDK 17 or newer, put these [Maven Central][maven] artifacts in `$jars`.

| Artifact | SHA-256 |
| --- | --- |
| `org.apache.parquet:parquet-column:1.16.0` | `034ec38dc4c58a0677bdaed666c9a7a8c68c269cce0d61dce4b7b49f7a0b9d7e` |
| `org.apache.parquet:parquet-common:1.16.0` | `7c7d120b83c923f9f5044e53518e6e8cc26d7993b89051b2a9979c3afdbc7811` |
| `org.apache.parquet:parquet-encoding:1.16.0` | `da7b8f3a458871e70de6f883539a39d8dc9e8ec67312d3b95ea1dbca4b68f5b3` |
| `org.slf4j:slf4j-api:1.7.33` | `336811855ee97fcd8413343dc42f4d26362502860e8a9193e4db305e3e8ef80a` |
| `org.slf4j:slf4j-nop:1.7.33` | `b3d68ed3f48f89b15e610b42efd72d3413316a07f5ba4ab4589fc449c9cb4beb` |

```sh
set -o pipefail
java -cp "$jars/*" scripts/parquet-hybrid/HybridOracle.java |
  diff -u tests/formats/parquet-hybrid/parquet-java-1.16.0.tsv -
lake build --wfail +Silmaril.Formats.Parquet.Hybrid.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.Hybrid.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#RLE
[java]: https://github.com/apache/parquet-java/tree/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/column/values/rle
[oracle]: ../../scripts/parquet-hybrid/HybridOracle.java
[vectors]: ../../tests/formats/parquet-hybrid/parquet-java-1.16.0.tsv
[lean]: ../../Silmaril/Formats/Parquet/Hybrid/Examples.lean
[maven]: https://repo.maven.apache.org/maven2/
