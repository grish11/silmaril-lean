# Checked Zstandard single frames

`Compression.Zstd.CheckedFrame.decode` accepts one exact RFC 8878
standard frame with raw, RLE, and supported type-2 blocks. For type 2,
the profile accepts raw or RLE literals followed by a zero sequence
count. Block decoding stops at the first last-block bit. A known
`Frame_Content_Size` must match the output. When the checksum flag is
set, exactly four trailer bytes must equal the low 32 bits of XXH64
over the decoded content, in little-endian order. A frame without a
checksum flag must end immediately after its last block.
[RFC 8878 §3.1.1][frame] · [Literal-only blocks][literal] · [Definitions][defs]

The caller sets independent compressed-input, decoded-output and
window limits. The decoder checks the input extent and window before
decoding blocks. Each block checks its size against the smaller of
the frame window and 128 KiB. Raw and type-2 blocks consume their
declared compressed extents. RLE consumes one byte and interprets its
size as the regenerated length. Each block receives the remaining
output budget. Raw and RLE check their sizes before copying or
expanding, and type 2 checks the regenerated literal count before
expansion. The decoder scans the supplied input list for its length
and accumulates decoded chunks before assembling the output. The
contracts bound byte counts.

`readBlock_sound` proves the exact body extent and output bound for a
successful block. `readBlocks_sound` proves the block chain ends at
the first last-block bit and its combined output fits the supplied
budget. `decode_sound` composes these with the existing
`parseHeader` semantics, exact trailer consumption, declared size
equality, verified checksum, and all three caller limits.
[Theorem header][thms]

Nonzero dictionary IDs return `unsupportedDictionary`. Nonzero
sequences and Huffman or treeless literal tags return
`literalBlock (.unsupported ...)`. Reserved block types, truncated
extents, checksum mismatch, and extra bytes have their own failures.
Skippable frames are outside the standard-magic profile and return
`badMagic`. Concatenated frames return `trailingInput` after the
first supported frame. This API is separate from the existing
Zstandard stream decoder. Parquet ZSTD remains unsupported because
ordinary compressed streams can require the missing entropy and
sequence machinery. [Parquet coverage][matrix]

## Independent fixtures

The differential uses libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. The reference driver
generates standard raw frames with and without a checksum, plus an
ordinary sequence-bearing frame, using the public compression API.
For the mixed frames, the driver produces the type-2 literal
sections using libzstd's literal writers. The oracle adds the zero
counts, writes the block headers and takes the checksum bytes from
an independent checksummed libzstd frame over the same plaintext.
The native decoder checks every assembled frame.
[libzstd source][zstd] · [Differential runner][oracle]

| Accepted fixture | Frame SHA-256 |
| --- | --- |
| native-empty | `6fb8543883dafcc2ed0934866b8b3f775231f5b0933add08bf502e9e84944cbd` |
| native-raw | `054ddbe66438c7a01d8daf2fd17f572fd49151b403a1d976c1b19082d1936d47` |
| native-checksum | `83243958e27ce54dcd72f17b7fe41862f4a4590810548834f1f4fd5eab581ade` |
| mixed-blocks | `bf592c35904f9689553d750f6f287ee4200e5a8d604a500d1d6028b41931baa3` |
| mixed-checksum | `cd2792524286c3eec3737d9a345749a8e3369a6a2a1ed0d23882296352cb56a8` |
| window-block-boundary | `35e1d21270a7126dfdd1d7563a1ef1e6c61ebc23a5ddd31b3e33af39de86ae05` |
| zero-output-final-block | `ad6afeb39ab01cfc32b0dfc5c8ffb4d7ea1190087dca23bf2296544a16b7e871` |

The oracle also checks bad block and checksum extents, a damaged
checksum, wrong declared content size, a nonzero dictionary ID,
unsupported sequences, trailing data, concatenated and skippable
frames, and all three caller caps. It prints the frame and output
digests. The Lean regression module additionally checks the
two-byte content-size field, the literal-tag rejections, and a
zero-output type-2 block after the output budget is exhausted.
[Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.CheckedFrame.Thms +Silmaril.Formats.Compression.Zstd.CheckedFrame.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-literal-oracle/check_frame.py
```

[frame]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1
[literal]: zstd-literal-block.md
[defs]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Tests.lean
[matrix]: arrow-parquet-coverage.md
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
[oracle]: ../../scripts/zstd-literal-oracle/check_frame.py
