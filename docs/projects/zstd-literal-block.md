# Bounded Zstandard literal-only compressed blocks

`Compression.Zstd.LiteralBlock.decode` takes an exact type-2
`Compressed_Block` body, a frame header, and an output cap. It reads raw
and RLE literal sections with each of the three regenerated-size
encodings. It accepts a zero sequence count only if the count consumes
the entire remaining body. In particular, the two-byte encoding
`80 00` computes a zero count and is accepted by the pinned oracle.
[Block size and type][blocks] · [Literal section][literals] · [Sequence count][sequences]

The caller supplies the header and the exact body slice. The input
extent must fit the smaller of the frame window and 128 KiB. The
regenerated size must fit both that same frame maximum and the caller
cap. The extent scan stops at the first byte past the maximum, and the
literal size is checked before splitting raw bytes or expanding an RLE
run. These are byte-count contracts.

The public theorems `parseLiterals_sound` and `readSequenceCount_sound`
give the RFC wire relations and exact remainder for the two sections.
`decode_sound` relates the entire body to its decoded literals and
proves the compressed and regenerated size bounds. The sequence-count
parser also covers nonzero counts as preparation for a sequence decoder.
[Definitions][defs] · [Theorems][thms]

Huffman and treeless literal sections and nonzero sequences produce
`unsupported` as soon as their tag or count is known. Those paths do
not validate the rest of the section. Truncation, trailing bytes after
a zero count, and both extent limits have separate errors. Frame
integration, sequence tables and execution, and a writer are outside
this profile. The existing frame decoder handles raw and RLE *frame
blocks*. Parquet ZSTD (codec ID 6) still returns `unsupportedCodec`
because ordinary Zstd frames require the remaining compressed-block
machinery. [Existing frame decoder][frame] · [Parquet coverage][matrix] ·
[Parquet ZSTD][parquet]

## Independent fixtures

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. Its upstream
`ZSTD_noCompressLiterals` and `ZSTD_compressRleLiteralsBlock`
generate the raw and RLE sections. The driver appends the zero sequence
count and wraps each block in a single-block frame with a 128 KiB
window. The native frame decoder and Lean block decoder independently
check the bytes. The two alternate header encodings are hand-authored.
The suite also uses `ZSTD_compress` at level 3 on `abcde` repeated
512 times and extracts its only block. libzstd decodes the frame and
Lean reports unsupported sequences for the block body. The rejection
fixtures cover truncated literal and sequence fields, a trailing byte,
an insufficient output cap, and an overlarge compressed extent.
[libzstd source][zstd] · [Oracle driver][oracle] · [Lean regressions][tests]

| Accepted or unsupported fixture | Block body SHA-256 |
| --- | --- |
| raw-0 | `96a296d224f285c67bee93c30f8a309157f0daa35dc5b87e410b78630a09cfc7` |
| raw-31 | `a33ab6994107877426db72acf8a0f5a38d044b34a99dcc8d4d24e1c44f69815d` |
| raw-32 | `ba805c7b0634796627a5795ba753f840210a307fa677c3ef8af17bca8f1664b0` |
| raw-4095 | `4b0cf72cd6dcd9a91735170815e688e6b8b190df4fef7b313b777a8d66a7635f` |
| raw-4096 | `a4559d78a5944ff8a7b618f7ea80ccba45ad978653274dddda9f7b45badd530d` |
| rle-31 | `df78f283fe8aa4a65b648bebfbeeb7c7085a1d709af848f5c0d6139beab49d2d` |
| rle-32 | `bdb84d3a1f62370a742182dc08f541cf4e653207aeafe1d72dbfd1fe6007135b` |
| rle-4096 | `75734bf18502deb1a856802c286095dfba32d4e687b937b566dbec0a0d8da684` |
| rle-131072 | `a6d3c7ec6939e7511792c16bad325f7b89e7a61b121f81c8bf1cd976f631bcb9` |
| wide-short-value | `1ac37365ef9620d0f27966ab3706751764b838c021d374a1eb94fa4ca9bc5b94` |
| two-byte-zero-sequences | `2850c8d33fd88edc0bfc9cebae426ce11c4a9c45496bb67c255f5461fc02856f` |
| ordinary compressed frame | `dcc0289b868b719ea5a9d9ee52898e0eb5263ac5d968654754e8fe9c9e047966` |

The oracle prints the hashes of each generated body and successful
decoded output. It needs Git, Make, a C and C++ toolchain, Python 3,
and the repository's pinned Lean toolchain.

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.LiteralBlock.Thms +Silmaril.Formats.Compression.Zstd.LiteralBlock.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-literal-oracle/check.py
```

[blocks]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.2
[literals]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.1.1
[sequences]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.2.1
[defs]: ../../Silmaril/Formats/Compression/Zstd/LiteralBlock/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/LiteralBlock/Thms.lean
[frame]: ../../Silmaril/Formats/Compression/Zstd/Defs.lean
[matrix]: arrow-parquet-coverage.md
[parquet]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md#zstd
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
[oracle]: ../../scripts/zstd-literal-oracle/check.py
[tests]: ../../Silmaril/Formats/Compression/Zstd/LiteralBlock/Tests.lean
