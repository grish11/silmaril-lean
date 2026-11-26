# Zstandard canonical Huffman tables and one reverse stream

`SingleStream.build` checks the input weights against
`DirectWeights.Tree.Valid`. It visits positive weights in ascending
order, with ascending literal value within each weight. Each symbol
occupies `2^(weight - 1)` consecutive slots. The start of that slot
range gives the left-aligned code, and every placement is checked
for alignment and range. The final range ends at the tree size.
[RFC 8878 §4.2.1.3][codes] · [Direct weights][weights] · [Definitions][defs]

`SingleStream.decode` takes a tree, the exact bytes of one stream and
its expected regenerated symbol count. It checks the stream byte and
output caps before reading bits. The decoder uses the existing reverse
reader to open the marker and match bounded canonical code fields.
It requires the exact requested count and no remaining payload bits.
The implementation searches the bounded table for each symbol.
[RFC 8878 §4.2.2][stream] · [Reverse bit reader][reverse]

`build_sound` connects construction to checked weights and the canonical
slot layout. `table_intervals` gives positive bounded widths and disjoint
intervals. `decode_sound` accounts for the end marker and every payload
bit, and proves both caller caps and exact regenerated count.
[Theorem header][thms]

The component takes a validated direct-profile tree and an already
delimited stream. FSE-compressed weights, four-stream jump-table
splitting, treeless table history, and frame or Parquet dispatch are
outside this slice.

## Pinned differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It compares every assigned
slot with the native X1 decode table and compares exact regenerated
literal bytes with `HUF_decompress1X1_DCtx_wksp`. Both literal payloads
come from frames produced and independently decoded by that library.
The oracle also compares all slots for depth 11 and the maximum
direct symbol count. [Pinned source][zstd] · [Oracle runner][oracle]

| Source frame | Literal bytes | Frame SHA-256 |
| --- | ---: | --- |
| Three-symbol source | 74 | `f1c72b9fdd1fb02a4b060883ff28becf6100c97f278aa74b06073a99c39c6bc6` |
| Four-symbol source | 168 | `32782f3912292b64c9ee3f89f056f7cd3b31009fe88a2eff150dee9dfd46e9af` |

The RFC's Table 25 assigns `0000` to literal 4 and `0001` to literal 5.
Its printed bytes `10 0d` decode to `[0, 1, 5, 4]` in both implementations.
The bytes `01 0d` proposed in reported erratum 8195 decode to
`[0, 1, 4, 5]`. Both implementations reject a zero marker, a truncated
payload and mismatched expected counts. Lean also checks caller caps.
[RFC erratum 8195][erratum] · [Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Thms +Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-stream-oracle/check.py
```

[codes]: https://www.rfc-editor.org/rfc/rfc8878#section-4.2.1.3
[stream]: https://www.rfc-editor.org/rfc/rfc8878#section-4.2.2
[erratum]: https://www.rfc-editor.org/errata/eid8195
[defs]: ../../Silmaril/Formats/Compression/Zstd/Huffman/SingleStream/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Huffman/SingleStream/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/Huffman/SingleStream/Tests.lean
[reverse]: ../../Silmaril/Formats/Compression/Zstd/ReverseBits/Thms.lean
[weights]: zstd-huffman-direct.md
[oracle]: ../../scripts/zstd-huffman-stream-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
