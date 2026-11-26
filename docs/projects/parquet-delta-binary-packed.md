# Bounded Parquet DELTA_BINARY_PACKED

`Silmaril.Formats.Parquet.DeltaBinaryPacked.Defs` reads one exact encoded
scalar slice. `parse physical limits expected source` returns a wire AST.
`decode` takes the same inputs and returns an ordered `List Int32` or
`List Int64` according to `physical`. `parsePrefix` returns the checked AST
and the untouched suffix of a bounded input. The caller supplies the
expected count, which is checked against the encoded count. The public
proof header is `Silmaril.Formats.Parquet.DeltaBinaryPacked.Thms`.

The wire specification is Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `Encodings.md` SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[DELTA_BINARY_PACKED wire rules][spec] · [Pinned parquet-java implementation][java]

## Wire and checked profile

- The header begins with ULEB128 block size, miniblock count, and total
  value count, followed by the ZigZag ULEB128 first value. Blocks begin
  with a ZigZag minimum delta and one width byte per miniblock. The reader
  uses canonical ULEB128 spellings. Header sizes and total count admit
  the nonnegative signed-i32 range. The first value and block minima
  admit the full signed physical width, including its minimum value.
- The block size is positive and divisible by 128. A positive miniblock
  count must divide it exactly and yield a positive multiple of 32 values
  per miniblock. Blocks cover the remaining deltas in order, with each
  nonfinal block full. Per-stream caller limits cap input bytes, logical
  values, values per block, miniblocks per block, and number of blocks.
- Active miniblocks store unsigned residuals in little-endian bit order at
  widths from zero through the physical width. Width zero contributes zero
  residuals with an empty payload. The reader checks the full active
  miniblock extent even when only some of its values are used. The unused
  residual bits in a partial miniblock may be arbitrary. A partial final
  block still has its complete width table. The unused width octets may be
  arbitrary and contribute no payload. The AST preserves both kinds of
  padding so its wire projection accounts for every input octet. The
  `blockValues` cap also bounds the work to unpack an active padded miniblock.
- Zero and one value use the complete header and no blocks. The first-value
  field is read in both cases and is ignored for zero values. Trailing
  bytes are rejected by the exact reader for every count. This degenerate
  profile matches the pinned parquet-java writer.
- Reconstruction adds the unsigned residual to the signed minimum and adds
  the result to the preceding value, wrapping to the physical width. The
  intermediate sum can be computed in `Int` because narrowing at the end
  gives the same residue as narrowing both sums. The preceding value
  carries across block and miniblock boundaries. The reader uses the
  encoded minima and widths without requiring minimal writer choices.

The executable decoder exposes `Header`, `Block`, and `Miniblock` as wire
structures. `Stream.wire` describes the exact bytes, including the unused
widths and the full payload of each active miniblock. `Header.first` and
`Block.minimum` read the signed interpretations of the stored ZigZag codes.
The API takes a bounded slice with a known expected count. Page layout,
compression, scanner integration, DELTA_BYTE_ARRAY,
logical annotations, and a Lean writer remain outside this reader.
The [DELTA_LENGTH_BYTE_ARRAY reader](parquet-delta-length-byte-array.md)
uses `parsePrefix` to split the length substream from its value suffix.
The byte cap covers the whole input, including the suffix.

## Public proofs

- `parse_sound` proves that the parsed AST accounts for the entire input,
  with valid header geometry, signed-field code bounds, exact block and
  miniblock coverage, and the caller's byte and value limits.
- `parsePrefix_sound` and `parsePrefix_consumed` identify the exact consumed
  prefix and remaining suffix. `parse_ok_iff` characterizes exact parsing by
  success with an empty suffix.
- `step_toInt` identifies the signed result of each reconstruction step as
  the balanced residue modulo `2^32` or `2^64`.
- `reconstruct_getElem` characterizes output position `i` by folding the
  first `i` deltas in wire order onto the signed first value.
  `reconstruct_length` and `decode_sound` give the exact output count.

## Independent fixtures

The [manifest][vectors] is produced by the [Java oracle][oracle], using
parquet-java **1.16.0** at commit `402c3810c372d29603e181771acebfecc71bef61`.
It checks the original scalar values with parquet-java's reader before
emitting the writer's bytes. The fixtures include zero and singleton
counts, signed wraparound with full 32- and 64-bit residual widths, a
multi-block stream with a negative minimum and nonzero unused width bytes,
and a 256-value block geometry with 128-value miniblocks.

Manifest columns are physical type, case name, block size, miniblock
count, value count, and hexadecimal scalar bytes. Its SHA-256 is
`a6138b4657791c99dc0750ad5123c78ab368938ad52eb9d699ffeefe2723543c`.
The [Lean examples][examples] bind those wire bytes and additionally test
arbitrary padding bits and unused widths, truncated active payloads or
width tables, invalid geometry and widths, count and limit errors,
noncanonical and out-of-range varints, and trailing bytes.

Use JDK 17 or later and the pinned jars from the [PLAIN fixture recipe][plain].
With `jars` set to that directory, run from the repository root.

```sh
set -o pipefail
java -cp "$jars/*" scripts/parquet-delta-binary-packed/DeltaOracle.java |
  diff -u tests/formats/parquet-delta-binary-packed/parquet-java-1.16.0.tsv -
lake build --wfail +Silmaril.Formats.Parquet.DeltaBinaryPacked.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.DeltaBinaryPacked.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#delta-encoding-delta_binary_packed--5
[java]: https://github.com/apache/parquet-java/tree/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/column/values/delta
[plain]: parquet-plain.md#independent-fixtures
[vectors]: ../../tests/formats/parquet-delta-binary-packed/parquet-java-1.16.0.tsv
[oracle]: ../../scripts/parquet-delta-binary-packed/DeltaOracle.java
[examples]: ../../Silmaril/Formats/Parquet/DeltaBinaryPacked/Examples.lean
