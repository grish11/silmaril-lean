# Direct Zstandard Huffman weight descriptions

`Huffman.DirectWeights.read` consumes a direct tree description at
the front of a Huffman literal payload. The header byte gives the
transmitted count as `header - 127`. The weight nibbles appear high
then low. The description ends at the next byte boundary, so an
odd transmitted count leaves the final low nibble unused. The reader
returns the rest of the payload unchanged. [RFC 8878 §4.2.1.1][rfc] · [Definitions][defs]

A positive weight contributes `2^(weight - 1)` slots. Zero denotes an
absent symbol. The sum of the transmitted slots determines the next
strictly larger power of two and the tree depth. The remaining slots
must form a positive power of two, which gives the inferred final
weight. The completed tree must have an even population of at least
two symbols in the deepest rank. Caller caps are intersected with
65 description bytes, 129 symbols including the inferred symbol, and
the RFC maximum depth of 11. [RFC tree and weight rules][weights]

`read_sound` proves the exact wire partition, nibble order and inferred
weight. It also proves the completed mass, weight bounds, deepest-rank
conditions and the caller's byte, symbol and depth caps. `suffix_exact`
recovers the untouched suffix by dropping exactly the reported
consumption. [Theorem header][thms]

This component supplies weights for a future Zstandard canonical
table builder. It rejects FSE-compressed weight descriptions with a
typed error. Canonical codes, reverse symbol decoding, four-stream
jump-table slicing and treeless table state are later components.
Frame and Parquet integration are outside this component.

## Pinned differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It extracts direct tree
descriptions from three compressed frames produced by the pinned
library and compares every decoded weight, depth, consumed byte
count and untouched literal-stream suffix with `HUF_readStats`.
Libzstd decodes the full frames to their original inputs. The
one- and four-stream labels describe the source frames.
[Pinned source][zstd] · [Oracle runner][oracle]

| Source streams | Direct prefix hex | Frame SHA-256 |
| --- | --- | --- |
| 1 | `8112` | `f1c72b9fdd1fb02a4b060883ff28becf6100c97f278aa74b06073a99c39c6bc6` |
| 1 | `821110` | `32782f3912292b64c9ee3f89f056f7cd3b31009fe88a2eff150dee9dfd46e9af` |
| 4 | `8611111110` | `a60a0d53fd2dbb2b32f7b0d6c748b01df3f34db2143774bd0618fbfd463f48bd` |

The oracle also compares the RFC example with nonzero padding,
a final weight greater than one, the maximum transmitted count and
depth 11. Both readers reject the truncated RFC example, zero mass,
a non-power remainder and an invalid deepest rank. Pinned
`HUF_readStats` accepts the depth-12 vector, which the Lean reader
rejects under the RFC depth ceiling. A library-produced FSE-weight
frame exercises the unsupported-mode error. [Lean regressions][tests] · [Oracle runner][oracle]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Thms +Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-direct-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-4.2.1.1
[weights]: https://www.rfc-editor.org/rfc/rfc8878#section-4.2.1
[defs]: ../../Silmaril/Formats/Compression/Zstd/Huffman/DirectWeights/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Huffman/DirectWeights/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/Huffman/DirectWeights/Tests.lean
[oracle]: ../../scripts/zstd-huffman-direct-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
