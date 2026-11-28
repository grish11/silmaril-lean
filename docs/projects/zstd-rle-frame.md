# Checked Zstandard frames with explicit RLE sequence tables

`CheckedFrame.Rle.decode` accepts one exact standard Zstandard
frame. It reuses the checked frame header and trailer logic.
Raw and RLE blocks are accepted. A type-2 block requires raw or
RLE literals and either zero sequences or three explicit RLE
sequence tables. The sequence decoder consumes the exact section.
The executor uses the resulting commands, literal buffer and
retained history. Declared frame size must match the output and
any checksum is verified before the decoder returns bytes.
[RFC 8878 frames][rfc-frame] · [RLE sequence sections][rle] · [Definitions][defs]

Each frame starts with empty history and repeat offsets
`(1, 4, 8)`. After each nonterminal block, history keeps the
last window of decoded bytes. Raw blocks, RLE blocks and
zero-sequence compressed blocks contribute bytes and preserve
the repeat offsets. Nonzero sequences update the offsets under
RFC 8878 §3.1.1.5. The executor requires positive distances
strictly smaller than `Window_Size` and within actual history.
[RFC 8878 distance rule][distance] · [Repeat offsets][offsets] · [Executor contract][execution]

The caller supplies compressed-input, frame-output, window and
per-block command caps. The decoder also checks block extents
against the RFC block maximum. Each block receives the
remaining frame-output budget. Before allocating commands,
the sequence decoder uses the smaller of the caller's command
cap and one third of the remaining block output capacity.
Each match requires at least three bytes. These bounds describe
byte counts and command counts.

`advance_sound` gives the exact retained suffix, its window
bound, and the updated repeat state. `advance_suffix` preserves
the suffix invariant for the whole frame prefix. `decode_sound`
relates the accepted frame to the chained block execution,
including every literal and sequence section, the per-block
command cap, exact frame extent, verified trailer, and the
frame limits. [Theorem header][thms]

Unsupported literal tags and sequence modes fail the frame.
Predefined tables, compressed FSE, repeat tables, and
mixed-mode tables remain unsupported. Repeat offsets are
carried across blocks independently of the sequence-table
mode. Nonzero dictionary IDs, skippable or concatenated frames
are outside the profile. Parquet ZSTD remains unsupported.

## Full-frame differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. Its literal writers
supply raw and RLE sections. The fixture writer supplies the
RLE sequence symbols, extra bits and frame framing. Checksummed
fixtures take the trailer from libzstd over the same plaintext.
Each accepted frame decodes to the same bytes in Lean and
libzstd. The mixed fixture sets repeat offset 6, crosses raw,
RLE and zero-sequence blocks, then uses the zero-literal
special repeat to resolve distance 5. The rolling-window
fixture crosses 1 KiB of output before a match at distance 1023.
[Oracle runner][oracle] · [Pinned libzstd source][zstd]

| Accepted frame | Frame SHA-256 |
| --- | --- |
| mixed-blocks-and-repeats | `047102c46907c678c9d89d105c8d3a1069ee7cca77a197f4970dcc889e67d32a` |
| mixed-blocks-and-checksum | `306cb3a7acd7674d33e78cc9a769f5d0b6dad5ff580bb317caf25fcbe4418f4c` |
| rolling-window | `a368f9c1241090619e2a188373f700e53fd7ce55b33673a4254406fce8df2673` |
| two-commands | `ebfb9b1b8d910d2fea2aa674b4db28605320e6d5ba5e7e27a580ce830bdcb7da` |
| zero-count-rle-literals | `7520bdb3dcb513610f6fc8d9b170aa6e37aa82c2acaa281f2d34c5dceaa58ab7` |

The native decoder accepts the companion fixture at distance
1024. Lean rejects it under the strict rule in §3.1.1.4.
A separate valid stream requests table repeat after RLE and
returns an unsupported-mode error in Lean, as does a native
predefined-table frame. Malformed controls cover block and
checksum truncation, an invalid reverse-bitstream end byte,
checksum mismatch, and trailing input. Additional controls
exercise all four caller caps.
[Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.CheckedFrame.Tests +Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-literal-oracle/check_rle_frame.py
python3 -I scripts/zstd-literal-oracle/check_frame.py
```

[rfc-frame]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1
[distance]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.4
[offsets]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.5
[rle]: zstd-rle-sequences.md
[execution]: zstd-sequence-execution.md
[defs]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Rle/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Rle/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Rle/Tests.lean
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
[oracle]: ../../scripts/zstd-literal-oracle/check_rle_frame.py
