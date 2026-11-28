# Exact Zstandard Huffman four-stream extents

`FourStream.split` takes the exact bytes starting at the six-byte
jump table, the declared byte count of that group, and the enclosing
literal section's regenerated size. The declared count includes the
jump table and the four streams. The enclosing tree description is
outside that count. The first three compressed extents are u16
little-endian fields. The fourth is the entire remaining suffix.
All four extents must contain at least one byte for the end marker.
[RFC 8878 §3.1.1.3.1.6][rfc] · [Definitions][defs]

The first three streams each regenerate `(regenerated + 3) / 4`
symbols. The fourth regenerates the balance and may be up to three
symbols shorter. The profile follows pinned libzstd's minimum of six
regenerated literals. At six, the fourth stream emits zero symbols
and still requires a marker-only stream. The input and output caps
are checked before slicing or decoding. [Pinned literal header][native-header]

`FourStream.decode` builds one table from the existing direct-weight
profile and uses the single-stream semantics on the four slices in
order. Each stream checks its own expected count, marker and exact
exhaustion. The stream error carries a one-based index.
`split_sound` establishes the byte partition, declared byte count,
caller caps and symbol quotas. `fourth_bounds` gives the range of the
final quota. `decode_sound` relates all four streams to the same checked
table and proves the exact joined size.
[Single-stream contract][single] · [Theorem header][thms]

The splitter is independent of Huffman table provenance and alphabet
size. This decoder uses the direct-tree profile's symbol cap. Future
FSE weights require the separate general 256-symbol tree boundary.
Literal-header parsing, treeless table history, frame dispatch and
Parquet activation are outside this slice.

## Pinned differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. Three library-produced frames
provide direct-weight four-stream literal sections in all three
four-stream size formats. It independently extracts the jump fields
and regenerated sizes, compares the Lean split, and compares the
joined literal bytes with `HUF_decompress4X_usingDTable`. Libzstd
also decodes the full source frames.
[Pinned source][zstd] · [Oracle runner][oracle]

| Size format | Compressed stream extents | Regenerated quotas | Frame SHA-256 |
| --- | --- | --- | --- |
| 1 | 30, 28, 29, 27 | 95, 95, 95, 92 | `fb668e404a428f3021a5caa6e63f5fbae479f7e3c19e15e77676c1fd59690c8c` |
| 2 | 206, 206, 206, 206 | 548, 548, 548, 548 | `a60a0d53fd2dbb2b32f7b0d6c748b01df3f34db2143774bd0618fbfd463f48bd` |
| 3 | 1799, 1799, 1801, 1798 | 4241, 4241, 4241, 4240 | `e08e1bef491b7ebca4150f176cbe860e9aa8d5f92f9630b0df73cb9d90dcc4ca` |

Both decoders accept a marker-only fourth stream at six symbols.
They reject a truncated jump table, zero first extent, extents that
overrun the group or leave no fourth stream, an invalid marker,
trailing bits and an incomplete code. Lean also checks both directions
of declared extent mismatch, the six-symbol minimum and caller caps.
[Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Thms +Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Tests +Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-four-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.1.6
[defs]: ../../Silmaril/Formats/Compression/Zstd/Huffman/FourStream/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Huffman/FourStream/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/Huffman/FourStream/Tests.lean
[single]: zstd-huffman-stream.md
[oracle]: ../../scripts/zstd-huffman-four-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
[native-header]: https://github.com/facebook/zstd/blob/f8745da6ff1ad1e7bab384bd1f9d742439278e99/lib/decompress/zstd_decompress_block.c
