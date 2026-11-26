# Parquet LZ4_RAW blocks

This profile implements Parquet's standardized `LZ4_RAW` codec for one
independent block. The caller supplies the compressed page slice and the
corresponding uncompressed size. Page layout, checksums, deprecated Hadoop
`LZ4` framing, LZ4 frames, and external dictionaries are outside the profile.
[Coverage matrix](arrow-parquet-coverage.md) · [Parquet 2.14.0 compression][parquet] ·
[LZ4 v1.10.0 block format][wire]

## Wire and validity

A sequence begins with a token. Its high nibble encodes the literal length.
Values 0–14 give the length directly. Value 15 requires an extension of zero
or more 255 bytes followed by a byte below 255. The sum of those bytes is
added to 15, even when the terminal byte is zero. The encoded number of
literal bytes follows.

A matched sequence then carries a two-byte little-endian offset. Its match
length is four plus the length field encoded by the low nibble, using the
same extension rule when that nibble is 15. The offset is in 1–65,535 and
cannot exceed the available history, including the sequence's literals.
Each copied byte reads the given distance from the output's current end.
A match can therefore read bytes it has just produced.

The last sequence contains only literals, and the block ends immediately
after them. The final low nibble has no match meaning for a nonempty
literal run. Empty input data is encoded as the single zero token. A
literal-only block can contain fewer than five bytes of output. For a
block with a match, the final run contains at least five literals and the
last match starts at least 12 uncompressed bytes before the end. The
second rule counts the last match's full length plus the final literal
length and allows equality.

## Bounds and proofs

`Bounds` supplies the exact `compressedSize` and `expectedSize` with
independent `compressedLimit` and `outputLimit`. Parsing checks both
limits first and then checks the supplied input extent. Each extension
and literal body is checked against remaining output room, and the final
sequence must use exactly that room. The decoder validates the offsets
and terminal conditions as it expands the AST from empty history. The
limits govern logical byte counts and work on the supplied slice.
Allocator overhead and a time bound are outside the theorem contract.

`Wire` relates the entire compressed slice to the AST, including the
token and extension fields. `Denotes` gives the expansion semantics
with the history checks and `TailValid`. Lean proves the following.

- `parse_sound` proves exact wire and size accounting within the limits.
- `denotes_length` proves that denotation adds the specified output length.
- `decode_sound` connects successful decoding to both relations, exact
  compressed and output lengths, and both limits.

The writer `encodeLiteral` emits one literal-only sequence with an exact
length extension when needed. Its interoperability evidence is
fixture-based. The general theorems cover the decoder. [Theorem header][thms]

## Differential and regression fixtures

The oracle runner fetches liblz4 v1.10.0 at the matrix pin
`ebb370ca83af193212df4dcbadcc5d87bc0de2f0` and compiles `lib/lz4.c` on
Linux using `-std=c99 -O2 -fPIC -shared`. It invokes
`LZ4_compress_default` and `LZ4_decompress_safe` independently of Lean.
The comparison requires the exact output size in addition to a
nonnegative liblz4 return value. Liblz4's return value is recorded when
it reports a shorter result under a larger capacity. The generated
inputs and authored byte fixtures use the repository's MIT license.
The reference library uses BSD 2-Clause. [Oracle runner][oracle] ·
[liblz4 license][license]

The runner checks both writer-to-reader directions and includes authored
controls for the extension terminators, the maximum 65,535-byte offset,
overlap, the exact 12-byte tail threshold and two separate tail
violations. It also covers truncated fields, trailing data and wrong
sizes. In the zero-offset control, pinned liblz4 returns bytes containing
a zero-filled match. The profile rejects the offset under the block
specification. Explicit caller-budget and extent failures have Lean
controls. The runner records SHA-256 digests for all wire fixtures.

Selected fixture fingerprints from the Linux differential run:

| Generator or control | Compressed block SHA-256 |
| --- | --- |
| liblz4 writer on `literal-fifteen` | `0dce37ed0a6581a1cefd6bbdd9851094a86ade08e2a0b42c6ef1ac8764ef5dcf` |
| liblz4 writer on `overlap-4096` | `176e7297e3abd053ced082d6ba3f67ab65b7cbe689b2749216056246a34d26e1` |
| `match-extension-chain` | `02ccb8b6ca8551107a4bd460bc5d78fdc8e0ef5ebd29621bf7f1f84a18f0224b` |
| `max-offset` | `c3ed74b813106ead11eb62d0b333abcc3a76cb2380bfb177ef50a541ee6b5b5d` |
| `tail-start-eleven` | `090f4eae8feaa8d7c8722dce7b575b2a2ae8ad36abf0b3f67e18b9f161c0db0c` |
| `zero-offset` | `ed2ecac7f14d17ec1a4f53208679f2daea04b606afd946f3cf953f69370eca9e` |

`Silmaril.Formats.Compression.Lz4Raw.Tests` carries the kernel-reduced
examples and executable guards in the existing library glob. The
standalone differential is run separately. [Lean regression module][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Lz4Raw.Thms +Silmaril.Formats.Compression.Lz4Raw.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/lz4-raw-oracle/check.py
```

[parquet]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md#lz4_raw
[wire]: https://github.com/lz4/lz4/blob/ebb370ca83af193212df4dcbadcc5d87bc0de2f0/doc/lz4_Block_format.md
[license]: https://github.com/lz4/lz4/blob/ebb370ca83af193212df4dcbadcc5d87bc0de2f0/lib/LICENSE
[thms]: ../../Silmaril/Formats/Compression/Lz4Raw/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Lz4Raw/Tests.lean
[oracle]: ../../scripts/lz4-raw-oracle/check.py
