# Checked Zstandard frames with sequence tables

`CheckedFrame.Sequences.decode` accepts one dictionary-free standard
frame. It reuses the checked frame envelope and plain block decoder.
A compressed block is sliced at its declared wire size and passed to
`CompressedBlock.decode` with the current history, tables, repeat
offsets and remaining frame output budget. Physical raw and RLE
blocks advance the history while preserving the tables and offsets.
The first last-block flag ends block dispatch. The envelope checks any
declared content size and checksum and requires exact trailer
consumption. [RFC 8878 §3.1.1][rfc] · [Frame entry point][defs] · [Block decoder][block]

The profile supports raw and RLE literals in compressed blocks, with
predefined, RLE, transmitted FSE and Repeat sequence tables.
Table Repeat requires a previous accepted table. It carries across
empty and plain blocks. The decoder has distinct errors for Huffman
and treeless literals, nonzero dictionary IDs, skippable frames,
reserved block types and trailing bytes. Concatenated frames are
outside the exact single-frame profile. Parquet activation is
separate.

`decode_sound` proves the exact frame and block chain, declared
content size, checked trailer and input, output, and window limits.
`readBlock_sound` proves exact consumption and a valid successor
within the remaining output budget. `block_history` identifies
the successor history as the exact last window of prior history
plus the accepted block output. [Theorem header][thms]

## Window boundary

This profile follows RFC 8878 §3.1.1.4's `distance < Window_Size`
rule. The pinned libzstd accepts the fixture at equality. Lean returns
`offsetOutsideWindow`. Both decode the otherwise equivalent fixture
at `Window_Size - 1`. This is a remaining interoperability difference
with pinned libzstd. [RFC sequence execution][window] · [Oracle runner][oracle]

## Pinned differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. Accepted frames include
the nine-block Repeat and history fixture with and without checksum,
a library-produced frame with raw/RLE literals, content size and
checksum, and the rolling-window fixture below the boundary.
The nine-block fixture is also checked by the standalone payload
oracle. [Pinned source][zstd] · [Block fixture][block]

| Frame | SHA-256 |
| --- | --- |
| Nine-block Repeat and history | `19ee42fd68fee802f5df505b2449c033b9b58aa5769da54bbcfb61b0bb2b3ad4` |
| Nine-block checksum | `1514d2176f4420ef2752eaa2ace86b04527ea2a26ee61bdbd51771c6fef008d9` |
| Library produced with declared size and checksum | `57edaeb1070e45d963392a1590fd12d6175cbcfd8716a76300ae00fe67c99bc8` |
| Distance one below window | `a368f9c1241090619e2a188373f700e53fd7ce55b33673a4254406fce8df2673` |
| Distance equal to window | `86bf5f8a4e683fb0ecab88bf8d8d3ea233de549150e24328bdd8db66036432e0` |
| Library produced with Huffman literals | `1d8107a07c3cca401da784a21de3ca46ae7a4054b209e982c0ab1e03ad0eae83` |

Both implementations reject malformed compressed extents, a missing
checksum byte, wrong checksum or content size, a trailing byte,
an unavailable dictionary and a bad marker after a valid table
prefix. The Lean entry point additionally checks the four caller
limits and classifies actual library-produced Huffman literals
as unsupported. [Oracle runner][oracle] · [Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences.Thms +Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-sequence-frame-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1
[window]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.4
[defs]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Sequences/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Sequences/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Sequences/Tests.lean
[block]: zstd-compressed-block.md
[oracle]: ../../scripts/zstd-sequence-frame-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
