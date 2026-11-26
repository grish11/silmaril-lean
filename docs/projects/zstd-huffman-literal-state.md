# Checked Zstandard literal table state

`Huffman.LiteralState.read` consumes one literal-section prefix. It
returns the literals, the exact number of consumed bytes, the untouched
suffix and the accepted successor state. Compressed and regenerated size
limits can vary between calls. The tree-validation profile is fixed in
the state type. [RFC 8878 §3.1.1.3.1][rfc] · [Definitions][defs]

| Literal tag | Table transition |
| --- | --- |
| Raw or RLE | Preserve the prior state and the existing compact literal representation |
| New tree | Install the exact checked canonical table after the literal streams succeed |
| Treeless | Decode with the prior checked table and preserve the state |

A dictionary-free frame starts with `State.empty`. A correctly bounded
treeless envelope with empty state returns `unavailableTable`. Treeless
format uses the compressed header and its declared extent, followed
immediately by the stream or jump table. The tree reader runs only for
a new-tree section. A failed section produces an error without a successor.

Input limits cover the literal header and stored payload, and output limits
cover the regenerated literals. Both intersect the existing 128 KiB
ceiling. The raw/RLE branch shares the literal size reader and payload
parser with `LiteralBlock.parseLiterals`. The new bounded entry checks the
entire raw/RLE extent before slicing. The original raw/RLE and type-2-only
Huffman entry points retain their contracts. This API ends at literal
sections. Dictionary loading, sequences, block execution and frame
dispatch are separate. [Raw/RLE reader][plain] · [Type-2 reader][fresh]

The state constructor is private. The retained table carries an erased
witness of a successful `TreeDescription.readTable` at the fixed profile.
`LiteralState.table_checked` recovers its validated tree and canonical
wire relation. `LiteralState.read_sound` gives the mode-specific transition,
exact output count and limits. The new-tree wire branch relates the installed
table to the exact input tree, and the treeless and plain branches return
the same prior state. `LiteralState.consumption_exact` and
`LiteralState.suffix_exact` account for all consumed bytes and the original
suffix. `LiteralState.unavailable_after_reset` specifies rejection of a valid
envelope with no installed table. [Theorem header][thms]

## Pinned differential

The runner builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It compresses 135,168 deterministic
bytes at level 3 and pins the resulting dictionary-free frame SHA-256
`6fb53d7c3100b6c9c30c275f3c7bb02fba4fd5ebb8dd96bcc4078ade9f24d73e`.
Native full-frame decoding matches the input. The native literal decoder
processes both compressed blocks in one context. Lean receives each full
block body and checks both section extents, literal outputs and following
suffixes. [Pinned source][zstd] · [Fixture manifest][manifest]

| Section | Format | Consumed bytes | Regenerated literals | Following bytes |
| --- | --- | --- | --- | --- |
| New direct tree, four streams | 2 | 562 | 1833 | 48746 |
| Treeless, one stream | 0 | 25 | 71 | 1535 |

The reset control rejects the second section in both readers. Native reports
`ZSTD_error_dictionary_corrupted` for the missing table and Lean reports
`unavailableTable`. Interposing independently authored raw and RLE sections
leaves the next treeless output identical. Lean checks the raw and compact
RLE values, exact raw/RLE suffix and unchanged table, and rejects one-less
compressed input and regenerated-output caps on the real pair. Unit cases
cover four-stream treeless reuse, replacement, malformed new-tree streams,
and truncation before table selection. [Oracle][oracle] · [Lean tests][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Tests +Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Tests +Silmaril.Formats.Compression.Zstd.LiteralBlock.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-literal-state-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.1
[defs]: ../../Silmaril/Formats/Compression/Zstd/Huffman/LiteralState/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Huffman/LiteralState/Thms.lean
[plain]: ../../Silmaril/Formats/Compression/Zstd/LiteralBlock/Defs.lean
[fresh]: zstd-huffman-literal-section.md
[tests]: ../../Silmaril/Formats/Compression/Zstd/Huffman/LiteralState/Tests.lean
[zstd]: https://github.com/facebook/zstd/blob/f8745da6ff1ad1e7bab384bd1f9d742439278e99/lib/decompress/zstd_decompress_block.c#L126
[manifest]: ../../scripts/zstd-huffman-literal-state-oracle/fixture.json
[oracle]: ../../scripts/zstd-huffman-literal-state-oracle/check.py
