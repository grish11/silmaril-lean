# Checked Zstandard Huffman tree descriptions

`Huffman.TreeDescription.read` reads a tree descriptor at the start of a
literal payload. A header of at least 128 selects direct nibble weights.
A header from 1 through 127 selects bounded interleaved FSE weights. The
reader reserves one symbol position for the inferred final weight before
FSE emission, then calls `Weights.complete` on the explicit weights.
Both encodings produce the same tree type and preserve the exact
literal-stream byte suffix. [RFC 8878 §§4.2.1–4.2.1.3][rfc] · [Definitions][defs]

| Encoding | Description byte ceiling | Completed symbol ceiling |
| --- | --- | --- |
| Direct | 65 | 129 |
| FSE | 128 | 256 |

Both byte ceilings include the header. Both symbol ceilings include the
inferred weight. Caller limits can lower either ceiling and the RFC
depth cap of 11. FSE emission and tree completion have distinct errors.
A valid FSE trace can still produce zero mass, a non-power remainder, or
an invalid deepest rank. `readTable` builds the shared canonical table
and returns it alongside the same prefix. The component ends before
literal stream decoding and block dispatch.
[Direct reader][direct] · [FSE emission][fse] · [Tree completion][weights]

`read_sound` proves the branch's wire relation, full tree validity and
byte cap. `completion_wire` gives the last-weight and slot-mass witness
with the transmitted list. `tree_unique` proves that any valid completion
of that list equals the returned tree. `suffix_exact` proves the byte
boundary, and `readTable_sound` proves canonical placement over the
exact checked prefix. [Theorem header][thms]

## Pinned differential

The runner builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It extracts a direct descriptor
and both previously pinned FSE descriptors from library-produced frames.
The completed weights, including the inferred weight, and description
extent are compared with `HUF_readStats`. Every lookup slot is compared
with `HUF_readDTableX1_wksp` at the encoded depth. The runner also checks
the original literal suffix, one-less caller caps, and a sparse direct
descriptor at both direct ceilings. [Pinned source][zstd] · [Runner][oracle]

| Encoding and completed symbols | Bytes | Depth | Description SHA-256 | Canonical slots SHA-256 |
| --- | --- | --- | --- | --- |
| Direct 3 | 2 | 2 | `1017fea2f9d51b66ef731df899ba9cb75a0e9348de5242322b02c9bf858cf014` | `ceb04abc9a0af42ad050bb6cfe6b693d046ebedaee8a11cc0bb2338a354dc8cb` |
| FSE 160 | 36 | 10 | `ccf34a085d6cadb19e7680e300043fd1e6ef8cc71c9ea0ff7b4203fbd2a02184` | `75befb31467618b8e892e5dee9cf19e308f2c4e470568411faaae9c83e5de6bf` |
| FSE 256 | 36 | 11 | `5da82e8ceb7e92b11f9cf9ad5eb80f96648eec4a7094268d1d702c0953b0cbf7` | `90ca7dc39bc498ad556f241dc751cd546e662d8a38d8c7f9b62c63be26d4937e` |
| Direct 129 | 65 | 1 | `d147e44d048d3874aac591dec58fb70f3a706c23362899f4101898dd31f4f2bc` | `b02c99eb6b751b979028860730799fc6e99aeffdd1be256b04629baf53ecd41e` |

Three hand-built reverse streams use `FSE_writeNCount` prefixes for
log-5 tables `[16,16]` and `[0,16,0,16]` and a log-6 table `[15,16,33]`.
The raw native FSE decoder and the Lean emission layer accept all three.
The completed-tree readers reject them. [Lean regressions][tests]

| Description hex | Explicit weights | Lean completion error |
| --- | --- | --- |
| `04 10 3f 02 04` | `0 0` | `zeroMass` |
| `06 10 88 c1 07 60 04` | `3 1` | `nonPowerRemainder` |
| `05 01 45 3f cc 12` | `2 2` | `invalidDeepestRank` |

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Tests +Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Tests +Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Tests +Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-tree-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-4.2.1
[defs]: ../../Silmaril/Formats/Compression/Zstd/Huffman/TreeDescription/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Huffman/TreeDescription/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/Huffman/TreeDescription/Tests.lean
[direct]: zstd-huffman-direct.md
[fse]: zstd-huffman-fse-weights.md
[weights]: zstd-huffman-weights.md
[oracle]: ../../scripts/zstd-huffman-tree-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
