# Zstandard new-tree compressed literal sections

`Huffman.LiteralSection.read` accepts literal block type 2. It reads exactly
the header and its declared compressed body, then returns the regenerated
literals and the untouched following bytes. The two size fields are
little-endian. The compressed field includes the tree description and,
for four streams, the jump table.
[RFC 8878 §3.1.1.3.1][rfc] · [Definitions][defs]

| Size format | Header bytes | Bits per size | Streams |
| --- | --- | --- | --- |
| 0 | 3 | 10 | 1 |
| 1 | 3 | 10 | 4 |
| 2 | 4 | 14 | 4 |
| 3 | 5 | 18 | 4 |

The input cap counts the header plus the compressed body. The output cap
counts regenerated literals. Both are intersected with 128 KiB and checked
before slicing the body or decoding literals. The checked tree reader
handles direct and FSE descriptions. Its suffix supplies the one stream
or the four-stream jump table and streams. Each reverse stream starts at a
checked end marker and exhausts its payload bits after regenerating its quota. The four-stream path
uses the pinned libzstd minimum of six literals and accepts a marker-only
fourth stream when its quota is zero.
[Tree reader][tree] · [Four-stream profile][four]

`LiteralSection.readHeader_sound` proves the header size and both extracted
fields. `LiteralSection.read_sound` witnesses the header, compressed extent,
checked tree and canonical table, exact stream extents, and regenerated count
under both caps. `LiteralSection.suffix_exact` identifies the byte suffix.
The checked-table entry point `FourStream.decodeTable` reuses the established
four-stream split and readers, with `FourStream.decodeTable_sound` preserving
their wire relation.
[Theorem header][thms]

Raw, RLE, and treeless tags have separate typed profile rejections. This
adapter stops at literal expansion. Treeless table reuse, sequence decoding,
block execution, and frame integration are separate.

## Pinned differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It extracts the first
compressed block of each library-produced frame and invokes the
library's `ZSTD_decodeLiteralsBlock_wrapper` with a fresh context. The
comparison checks consumed bytes and every literal against the native
results, and checks that Lean returns all bytes following the native
boundary. Full native frame decode also matches each original input.
[Pinned source][zstd] · [Runner][oracle]

| Format and tree | Section bytes | Literals | Frame SHA-256 | Section SHA-256 |
| --- | --- | --- | --- | --- |
| 0 direct | 21 | 74 | `f1c72b9fdd1fb02a4b060883ff28becf6100c97f278aa74b06073a99c39c6bc6` | `b028c0032559dab7dba22f4dedd55423e8d002ebd81ec1dc48fe80517ddadab4` |
| 0 FSE | 56 | 186 | `af70548698bcd138aed5f781b24802fcaa1a5044b67bd1c3c9df3e5c123d3ed4` | `d9cf4c365ee70805e58b2723d4b81ca456a64741411ca1d7eb13410aae90d9c9` |
| 1 direct | 126 | 377 | `fb668e404a428f3021a5caa6e63f5fbae479f7e3c19e15e77676c1fd59690c8c` | `cd4214aa26fffaee117d7403f81f96cb6ade0b0e31468354c549dc033fc929ac` |
| 2 direct | 839 | 2192 | `a60a0d53fd2dbb2b32f7b0d6c748b01df3f34db2143774bd0618fbfd463f48bd` | `1286fca33c80a8542ff269db46bd05f971265fe7c4a888d11db6cdb560c5817b` |
| 3 direct | 7214 | 16963 | `e08e1bef491b7ebca4150f176cbe860e9aa8d5f92f9630b0df73cb9d90dcc4ca` | `b260d4adda3da096aaf97c1ab007c284e7af4aea4e58e5458c0f32aafd0b72d4` |
| 3 FSE | 34916 | 48256 | `41cf51c4513aef112c218d0202dc21a2ba336cdfa9b9c2b0e944fde83b6fd75b` | `a44dc1dbef34ea09b0d09bd654ea299986dd537da58448311bd6764ffa5aa703` |

Hand-built valid controls include a marker-only single stream and a
marker-only fourth stream. Rejections cover truncated headers or bodies,
invalid direct and FSE tree completions, the jump extent, wire exhaustion,
regenerated size, and a fresh context encountering a treeless tag. Lean
also checks the separate raw and RLE profile rejections and the input and
output caps. [Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Tests +Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Tests +Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Tests +Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-literal-section-oracle/check.py
python3 -I scripts/zstd-huffman-four-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.1
[defs]: ../../Silmaril/Formats/Compression/Zstd/Huffman/LiteralSection/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Huffman/LiteralSection/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/Huffman/LiteralSection/Tests.lean
[tree]: zstd-huffman-tree-description.md
[four]: zstd-huffman-four-stream.md
[oracle]: ../../scripts/zstd-huffman-literal-section-oracle/check.py
[zstd]: https://github.com/facebook/zstd/blob/f8745da6ff1ad1e7bab384bd1f9d742439278e99/lib/decompress/zstd_decompress_block.c#L126
