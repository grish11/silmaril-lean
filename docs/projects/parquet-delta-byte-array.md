# Bounded Parquet DELTA_BYTE_ARRAY

`Silmaril.Formats.Parquet.DeltaByteArray.Defs` decodes one exact encoding-7
scalar slice. Call `decode limits expected source` with the present-value
count. The result is an ordered `List Bytes`. The public theorem header is
`Silmaril.Formats.Parquet.DeltaByteArray.Thms`.

The wire specification is Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `Encodings.md` SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[DELTA_BYTE_ARRAY wire rules][spec] · [parquet-java implementation][java]

## Wire profile and limits

1. Read a [DELTA_BINARY_PACKED][delta] INT32 prefix-length stream. The
   checked prefix parser leaves the remaining bytes untouched.
2. Decode that remainder as one exact [DELTA_LENGTH_BYTE_ARRAY][length]
   suffix stream. Both streams must declare the caller's expected count.
3. Starting with an empty predecessor, pair each prefix length with its
   corresponding suffix. Take exactly that many bytes from the preceding
   reconstructed value and append the full suffix. Use this reconstructed
   value as the next predecessor, including across delta block boundaries.

The first prefix length must be zero. Later prefix lengths must be
nonnegative and fit the previous value. The reader allows any prefix length
meeting those constraints. An empty suffix can reproduce a previous value.
An empty reconstructed value becomes the next predecessor just like any
other value. Zero values require both complete zero-count headers and no
payload. The underlying readers govern canonical varints, delta geometry,
padding, truncated data, and exact consumption.

`limits.prefixes.bytes` caps the whole input. The prefix and suffix readers
also enforce their respective count, geometry and encoded-byte caps, with
the suffix-specific caps starting at the suffix-length stream. Before
building each value, reconstruction checks that prefix length plus suffix
length is less than `2^31` and fits `limits.valueBytes` and the remaining
`limits.decodedBytes`. Size arithmetic uses `Nat`, so combined and cumulative
sizes cannot silently wrap. The cumulative limit counts every output value,
including bytes copied from its predecessor.

The reader interprets opaque bytes, including embedded zero octets and
invalid UTF-8. Its checked profile is variable-length BYTE_ARRAY. A client
claiming FIXED_LEN_BYTE_ARRAY also needs to check the schema width against each
result. Cross-page predecessor state, logical annotations, page dispatch,
scanner assembly, and a writer are outside the codec.

## Public proofs

- `reconstruct_ok_iff` gives the zero first prefix and an ordered
  `Reconstruction` derivation. Each step proves the prefix bound and
  exact previous-value prefix plus suffix, and passes the constructed
  value and reduced byte budget to its successor.
- `reconstruction_sizes` gives the count of paired lengths and suffixes
  and the cumulative output byte bound.
- `decode_sound` combines the prefix proof, the exact suffix decoder,
  and ordered reconstruction. The entire input consists of precisely
  the prefix-length wire, suffix-length wire, and concatenated suffix
  bytes. The byte extent and output count are explicit in the contract.

## Independent fixtures

The [manifest][vectors] is produced by the [Java oracle][oracle] using
parquet-java **1.16.0**, commit `402c3810c372d29603e181771acebfecc71bef61`.
The Java delta reader independently locates both stream boundaries and
checks the declared lengths. The DELTA_BYTE_ARRAY reader checks the
original values, and the oracle compares the raw remainder with the
concatenation of the expected suffixes. Fixtures cover the specification's
example, zero values and one empty value, opaque values, repeated long
prefixes, and a sequence spanning multiple delta blocks.

The TSV columns are case name, value count, end offset of the prefix-length
stream, start offset of raw suffix bytes, and hexadecimal scalar bytes. Its
SHA-256 is `52cd49ebc176d567ba23b5fc4faa99579fbb4497120406890cf21a4938cf7b13`.
The [Lean examples][lean] check both offsets and the decoded values. They
also cover negative and out-of-range prefixes, the first-prefix rule,
malformed lengths and exact extents, per-value and cumulative limits, and
the signed-i32 boundary without large allocations.

Use JDK 17 or later and the pinned jars from the [PLAIN fixture recipe][plain].
With `jars` set to that directory, run from the repository root.

```sh
set -o pipefail
java -cp "$jars/*" scripts/parquet-delta-byte-array/DeltaByteArrayOracle.java |
  diff -u tests/formats/parquet-delta-byte-array/parquet-java-1.16.0.tsv -
lake build --wfail +Silmaril.Formats.Parquet.DeltaByteArray.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.DeltaByteArray.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#delta-strings-delta_byte_array--7
[java]: https://github.com/apache/parquet-java/tree/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/column/values/deltastrings
[delta]: parquet-delta-binary-packed.md
[length]: parquet-delta-length-byte-array.md
[plain]: parquet-plain.md#independent-fixtures
[vectors]: ../../tests/formats/parquet-delta-byte-array/parquet-java-1.16.0.tsv
[oracle]: ../../scripts/parquet-delta-byte-array/DeltaByteArrayOracle.java
[lean]: ../../Silmaril/Formats/Parquet/DeltaByteArray/Examples.lean
