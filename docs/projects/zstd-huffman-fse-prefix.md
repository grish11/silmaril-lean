# Zstandard Huffman FSE description and initial states

`Huffman.FsePrefix.read` takes a Huffman literal payload beginning at its
tree descriptor. Header bytes 1 through 127 give the exact size of the FSE
description. The caller's byte cap includes the header. The reader slices the
description before parsing normalized counts or opening the reverse stream.
The suffix contains the original literal-stream bytes.
[RFC 8878 §§4.2.1–4.2.1.2][rfc] · [Definitions][defs]

The existing `FseTable.NCount.readTable` reads the byte-aligned count
prefix and builds the canonical FSE table. This profile allows an
accuracy log of 5 or 6 and symbols 0 through 11, the RFC Huffman
weight range. The normalized-count suffix is the exact extent of the
reverse stream. Its highest set bit in the final byte is the end marker.
The reader initializes State1 for the even-indexed weights, then State2 for
the odd-indexed weights, with one field of table-log width per state.
[Count reader][ncount] · [Reverse reader][reverse]

`FsePrefix.read_sound` proves the exact extent, normalized-count wire
relation, shared table layout and well-formedness, at most 64 rows, and
both initial state indices in range. It also specifies the ordered fields,
their bit values, and the exact unread reverse bits. `FsePrefix.suffix_exact`
identifies the untouched literal bytes. Empty, direct, truncated, over-cap,
and malformed descriptions have typed errors. The API stops at initialization.
Interleaved transitions, terminal overflow, inferred weights and literal
or frame dispatch are separate steps. [Theorem header][thms]

## Pinned differential

The runner builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99` and reproduces the two frames
from the general Huffman weight fixtures. It compares the description
extent, normalized counts and every state row with `FSE_readNCount` and
`FSE_buildDTable_wksp`. It compares the ordered states and the full unread
bit sequence with `FSE_initDState` and the native reverse-bit reader. It
also checks the untouched literal suffix. [Pinned source][zstd] · [Runner][oracle]

| Source tree symbols | Description bytes | Count bytes | Log | Initial states | Unread bits | Description SHA-256 |
| --- | --- | --- | --- | --- | --- | --- |
| 160 | 36 | 4 | 5 | (18, 27) | 234 | `ccf34a085d6cadb19e7680e300043fd1e6ef8cc71c9ea0ff7b4203fbd2a02184` |
| 256 | 36 | 4 | 5 | (9, 18) | 236 | `5da82e8ceb7e92b11f9cf9ad5eb80f96648eec4a7094268d1d702c0953b0cbf7` |

The synthetic log-6 setup `05 01 45 3f 93 13` uses count bytes produced by
`FSE_writeNCount` for `[15, 16, 33]` and a hand-built reverse stream that
ends immediately after state initialization. Both readers recover states
14 and 19 and all 64 rows. Negative controls cover the description extent,
wrong mode, truncated or out-of-profile counts, missing or zero marker,
and reverse streams too short for the first or second state. Lean also
checks the exact caller byte cap. [Frame hashes][weights] · [Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Tests +Silmaril.Formats.Compression.Zstd.FseTable.NCount.Tests +Silmaril.Formats.Compression.Zstd.SequenceDecode.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-fse-prefix-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-4.2.1.2
[defs]: ../../Silmaril/Formats/Compression/Zstd/Huffman/FsePrefix/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Huffman/FsePrefix/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/Huffman/FsePrefix/Tests.lean
[ncount]: ../../Silmaril/Formats/Compression/Zstd/FseTable/NCount/Thms.lean
[reverse]: ../../Silmaril/Formats/Compression/Zstd/ReverseBits/Thms.lean
[weights]: zstd-huffman-weights.md
[oracle]: ../../scripts/zstd-huffman-fse-prefix-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
